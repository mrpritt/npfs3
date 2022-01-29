#include <iostream>
#include <fstream>
#include <sstream>
#include <cstdlib>
#include <string>
#include <array>
#include <vector>
#include <algorithm>
#include <numeric>
#include <ctime>
#include <limits>
#include <cmath>
#include <cassert>

using std::vector;

////////////////////////////////////////////////////////////
// Source code of the algorithms proposed in the article:
// Fast heuristics for minimizing the makespan in non-permutation
// flow shops. Benavides, A.J. and Ritt, M., 2018. Computers &
// Operations Research, 100, pp.230-243.
//
// If you download and read this file, you are accepting that
// it is provided under the GNU General Public License v3.0
// available at http://www.gnu.org/licenses/gpl-3.0.en.html.
////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////
// The only hard-coded parameter selects the benchmark
// by uncommenting only one of the next three lines:
#define TAILLARD
// #define VRF_S
// #define VRF_L
////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////
// Compilation tested with the next flags:
// g++-7 -O2 --static --fast-math -std=c++17 -DNDEBUG
//   -Werror=implicit-fallthrough=0 -pedantic -Wall -Wextra -Wcast-align
//   -Wcast-qual -Wctor-dtor-privacy -Wdisabled-optimization -Wformat=2
//   -Winit-self -Wlogical-op -Wmissing-declarations -Wnoexcept
//   -Woverloaded-virtual -Wredundant-decls -Wshadow -Wsign-promo
//   -Wstrict-null-sentinel -Wstrict-overflow=5 -Wundef -Werror -Wno-unused
//   -Wold-style-cast -Wsign-conversion -Wswitch-default -Wmissing-include-dirs
//   pnpFSSP.cpp -o pnpFSSP;
////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////
// Data Types definitions

typedef uint_fast32_t t_time;      // 0,..., (n+m)tmax
typedef int_fast32_t t_operation;  // 1,2,..., mn   // 1: first operation; mn: last operation;
typedef int_fast32_t st_operation; // used to check signed conversions
typedef int_fast16_t t_job;        // 0,1,...,n-1   // j = (o-1)/mMach
typedef int_fast8_t t_mach;        // 1,2,..., m    // m = (o-1)%mMach +1
typedef uint_fast32_t t_size_type; // unsigned value in vector resize and reserve
typedef struct _solution t_solution;

// unfold-for acceleration
#define UNFOLDFOR2( __iters__, __sentences__ ) \
		switch ( __iters__ ) \
		{ \
			case 60: { __sentences__ } \
			case 59: { __sentences__ } \
			case 58: { __sentences__ } \
			case 57: { __sentences__ } \
			case 56: { __sentences__ } \
			case 55: { __sentences__ } \
			case 54: { __sentences__ } \
			case 53: { __sentences__ } \
			case 52: { __sentences__ } \
			case 51: { __sentences__ } \
			case 50: { __sentences__ } \
			case 49: { __sentences__ } \
			case 48: { __sentences__ } \
			case 47: { __sentences__ } \
			case 46: { __sentences__ } \
			case 45: { __sentences__ } \
			case 44: { __sentences__ } \
			case 43: { __sentences__ } \
			case 42: { __sentences__ } \
			case 41: { __sentences__ } \
			case 40: { __sentences__ } \
			case 39: { __sentences__ } \
			case 38: { __sentences__ } \
			case 37: { __sentences__ } \
			case 36: { __sentences__ } \
			case 35: { __sentences__ } \
			case 34: { __sentences__ } \
			case 33: { __sentences__ } \
			case 32: { __sentences__ } \
			case 31: { __sentences__ } \
			case 30: { __sentences__ } \
			case 29: { __sentences__ } \
			case 28: { __sentences__ } \
			case 27: { __sentences__ } \
			case 26: { __sentences__ } \
			case 25: { __sentences__ } \
			case 24: { __sentences__ } \
			case 23: { __sentences__ } \
			case 22: { __sentences__ } \
			case 21: { __sentences__ } \
			case 20: { __sentences__ } \
			case 19: { __sentences__ } \
			case 18: { __sentences__ } \
			case 17: { __sentences__ } \
			case 16: { __sentences__ } \
			case 15: { __sentences__ } \
			case 14: { __sentences__ } \
			case 13: { __sentences__ } \
			case 12: { __sentences__ } \
			case 11: { __sentences__ } \
			case 10: { __sentences__ } \
			case  9: { __sentences__ } \
			case  8: { __sentences__ } \
			case  7: { __sentences__ } \
			case  6: { __sentences__ } \
			case  5: { __sentences__ } \
			case  4: { __sentences__ } \
			case  3: { __sentences__ } \
			case  2: { __sentences__ } \
			default: { } \
		}

typedef uint_fast64_t t_elapsed;      // Defined as tenth of a millisecond
static double timeMeasure = 10000.0;  // Defined as tenth of a millisecond
inline t_elapsed elapsed(bool reset = false)
{
	static std::clock_t start = std::clock();
	if ( reset ) start = std::clock();
	return (timeMeasure*double(std::clock()-start))/double(CLOCKS_PER_SEC);
}

////////////////////////////////////////////////////////////
//	Global definitions

const t_job destroyNCm = 4;
const t_time max_time = std::numeric_limits<t_time>::max();
const t_operation no_op = std::numeric_limits<t_operation>::max();

t_job nJobs;       // number of jobs
t_mach mMach = 20; // number of machines
t_operation mnOps; // nJobs * mMach, this is also the last operation;
t_time psum;       // total sum of processing times of all operations

static vector < t_job > jobs; // previously used job permutation
static vector < t_time > p;   // processing times of operations [1, nJobs * mMach + 1]

static vector < t_time > Me0; // earliest completion times (heads)
static vector < t_time > Mq0; // latest starting times (tails)
static vector < t_time > Me1; // earliest completion time after insertion
static vector < t_time > Mq1; // latest starting time after insertion
static vector < t_time > MC0; // makespan of straight insertions
static vector < t_time > MC1; // makespan of insertions with anticipation
static vector < t_time > _LM; // helper

std::ofstream fout;       // out file stream

// NEH-BR insertion points
static vector < vector < t_operation > ::iterator > ins_bj; // best insert positions
static vector < int_fast8_t > ins_xp; // best cross point  // operation(s) with the minimal function value TFmin

// time report and time limit fixed controllers
#define TCHK 150
#define TLMT 450
// time report and time limit variable controllers
t_elapsed _timecheck = t_elapsed(TCHK*mnOps); // print information after this execution time
t_elapsed _timelimit = t_elapsed(TLMT*mnOps); // execution time limit

// statistic variables
t_time _max_ls_iters = 1;
t_time _tot_ls_iters = 1;
t_time _max_swap_size = 0;//must be 2*nJobs

////////////////////////////////////////////////////////////
//  Solution Structure for NON-PERMUTATION schedules

struct _solution {
	t_time Cm;// corresponding Cmax
	vector < t_operation > ops; // operation pairs that define a permutation of pseudo jobs .

	void print(std::ostream &o);

	void __PropagateMF0 ( vector < t_time > ::iterator & me, vector < t_time > ::iterator & lm );
	void __PropagateMF ( vector < t_operation > ::iterator & op, vector < t_time > ::iterator & me, vector < t_time > ::iterator & lm );
	void __PropagateMB0 ( vector < t_time > ::iterator & me, vector < t_time > ::iterator & lm,  vector < t_time > ::iterator & mf, vector < t_time > ::iterator & mq );
	t_mach __PropagateMB ( vector < t_operation > ::iterator & op, vector < t_time > ::iterator & me, vector < t_time > ::iterator & lm,  vector < t_time > ::iterator & mf, vector < t_time > ::iterator & mq );
	void __PropagateFi ( const t_operation & opb, const t_operation & ope );
	void _PropagateFi ( const vector < t_operation > ::iterator & opbegin );
	void Evaluate();
	#ifndef NDEBUG
	void Verify();
	void VerifyCm();
	#endif

	inline t_time CalculateCMs ( const t_operation jo );
	inline t_time CalculateCMs_NP ( const t_operation jo );
	vector < t_operation > ::iterator CalculateBJ( const t_operation jo );
	inline t_time CalculateCMs_LJP ( const t_operation jo );

	typedef void ( _solution::*_t_priority ) (vector < t_operation > & );
	typedef void ( _solution::*_t_InsertJob ) ( const t_operation );
	typedef void ( _solution::*_t_LocalSearch ) ();
	typedef void ( _solution::*_t_Construct ) (int_fast16_t sp);

	template < bool RandomInsertion = true >
	inline void InsertJobOp ( const t_operation );
	template < bool RandomInsertion = true >
	inline void InsertJobOp_NP ( const t_operation );
	inline void InsertJobOpFF ( const t_operation );
	inline void InsertJobOpFF_NP ( const t_operation );
	inline void InsertJobOpLJP ( const t_operation );

	inline void DeleteJob( const t_job );
	inline void Delete2Jobs( const t_job, const t_job );
	inline void DeleteJobs( const vector < t_operation > :: iterator &, const vector < t_operation > :: iterator & );

	inline void _NEH_priority ( vector < t_operation > & );
	inline void _AD_priority ( vector < t_operation > & );
	inline void _ADS_priority ( vector < t_operation > & );

	template < _t_InsertJob >
	inline void LocalSearch_Insertion();

	template < _t_InsertJob >
	inline void PairSearch_Insertion();

	template < _t_InsertJob, bool RandomInsertion = true >
	inline void LocalSearch_PRInsertionAll();

	template < _t_InsertJob, bool RandomInsertion = true >
	inline void LocalSearch_PRInsertionCrt();

	inline void LocalSearch_fastN5_Cm_NP();

	template < _t_priority , _t_InsertJob , _t_InsertJob >
	inline void Create_NEH_NP(int_fast16_t);

	inline void Create_F5_NP(int_fast16_t);
	inline void Create_RN_NP(int_fast16_t);
	inline void Create_Pa_NP(int_fast16_t);
	inline void Create_Pc_NP(int_fast16_t);

	template < _t_priority >
	inline void Create_BRN_NP(int_fast16_t);

};

////////////////////////////////////////////////////////////
// Load instance file and reserves memory according to size
void load_operations (std::string & file);
void load_operations (std::string & file)
{
	t_operation dmy;
	std::ifstream fin( file );
	fin >> dmy; nJobs = dmy;
	fin >> dmy; mMach = dmy;
	mnOps = nJobs * mMach;

	if (mnOps > 50000 || mnOps < 50) { std::cout << "instance file " << file << " is missing! " <<  mnOps << " operations!?!?" << std::endl; exit(9999); }
	assert (mnOps <= 50000 && mnOps >= 50);
	if (mnOps > 50000) return;
	p.resize(t_size_type(mnOps + 1));
	psum = 0;
	for(t_job j = 0; j < nJobs; ++j)
	{
		t_operation o = j * mMach;
		for(t_mach i = 1; i <= mMach; ++i)
		{
			fin >> dmy;
			fin >> dmy;
			p [ t_size_type (++o) ] = t_time(dmy);
			psum += p [ t_size_type(o) ];
		}
	}
	fin.close();

	jobs.resize(t_size_type(nJobs));
	iota ( jobs.begin(), jobs.end(), 0 );

	t_size_type ReserveSize = t_size_type(mnOps*3/2);
	#if defined TAILLARD
	if (nJobs == 500) ReserveSize = t_size_type(750*mMach);
	else if (nJobs == 200) ReserveSize = t_size_type(340*mMach);
	else ReserveSize = t_size_type(180*mMach);
	#elif defined VRF_S
	ReserveSize = t_size_type(120*mMach);
	#elif defined VRF_L
	ReserveSize = ( 20 + 221*t_size_type(nJobs)/100 - 7*t_size_type(nJobs)*t_size_type(nJobs)/10000 )*t_size_type(mMach);
	#else
	ReserveSize = ( 3*t_size_type(nmOps) );
	#endif

	Me0.resize(ReserveSize); Me1.resize(ReserveSize);
	Mq0.resize(ReserveSize); Mq1.resize(ReserveSize);
	MC0.resize(ReserveSize); MC1.resize(ReserveSize);
	for ( auto me  = Me0.begin() - 1, lm = me+mMach; me <= lm;) *(++me) = 0;
	ins_bj.reserve(t_size_type(3*nJobs));
	ins_xp.reserve(t_size_type(3*nJobs));
}

#ifndef NDEBUG
bool check_ops_order ( vector < t_operation > & ops );
bool check_ops_order ( vector < t_operation > & ops )
{
	static vector < t_operation > loJ(501);
	loJ.assign(t_size_type(nJobs+1),0);
	t_job lj = nJobs;
	for ( vector < t_operation > ::iterator o = ops.begin(), _o = ops.end(); o < _o;)
	{
		t_operation ob = *o;++o;
		t_operation oe = *o;++o;
		assert ( ob <= oe );
		t_operation j = (ob-1)/mMach;
		t_operation m = (ob-1)%mMach;
		assert ( lj != j );
		if ( m )
			assert( (loJ[t_size_type(j)] + 1 == ob) );
		else
			assert ( loJ[t_size_type(j)] == 0 );
		loJ[t_size_type(j)] = oe;
		lj = j;
	}
	for ( auto & oe : loJ )
	{
		if ( oe )
			assert ( oe % mMach == 0 );
	}
	return true;
}
#endif

void t_solution::print(std::ostream &o = fout)
{
	o << elapsed() << "\t" << Cm << "\t{";
	for ( auto op : ops )
		o << " " << op << "," ;
	o << "}" << std::endl;
}

////////////////////////////////////////////////////////////
//  propagators

inline
void t_solution::__PropagateMF0 ( vector < t_time > ::iterator & me, vector < t_time > ::iterator & lm )
{
	lm = Me0.begin() - 1;
	me = lm + mMach;
}

inline
void t_solution::__PropagateMF ( vector < t_operation > ::iterator & op, vector < t_time > ::iterator & me, vector < t_time > ::iterator & lm )
{
	// needs me, lm defined
	t_operation o = *(op);
	t_mach mc = (o-1) % mMach; //adjusted
	vector < t_time > ::iterator _me = me + mMach;

	UNFOLDFOR2 ( mc + 1 , { *(++me) = *(++lm); } );

	t_time lt = mc? *me: 0;
	vector < t_time > ::iterator t = p.begin() + st_operation(o);

	{ if ( lt < *(++lm) ) lt = *lm; lt += *t; *(++me) = lt; }
	UNFOLDFOR2 ( *(++op) - o  + 1 , { if ( lt < *(++lm) ) lt = *lm; lt += *(++t); *(++me) = lt; } );

	UNFOLDFOR2 ( _me - me + 1 , { *(++me) = *(++lm); } );
}

inline
void t_solution::__PropagateMB0 ( vector < t_time > ::iterator & me, vector < t_time > ::iterator & lm,  vector < t_time > ::iterator & mf, vector < t_time > ::iterator & mq )
{
	++me;
	st_operation delta = st_operation(ops.size()/2+1) * mMach;
	mq = lm = Mq0.begin() + delta;
	mf = Me1.begin() + delta;

	UNFOLDFOR2 ( mMach , { *(--mq) = 0; *(--mf) = *(--me); } );
	{ *(--mq) = 0; *(--mf) = *(--me); }
}

inline
t_mach t_solution::__PropagateMB ( vector < t_operation > ::iterator & op, vector < t_time > ::iterator & me, vector < t_time > ::iterator & lm,  vector < t_time > ::iterator & mf, vector < t_time > ::iterator & mq )
{
	// needs me, mq, lm, mf defined
	t_operation o = *(op);
	t_mach mc = mMach - (o-1) % mMach - 1; // adjusted reversed
	vector < t_time > ::iterator _mq = mq - mMach;

	UNFOLDFOR2 ( mc + 1 , { *(--mf) = *(--me) + ( *(--mq) = *(--lm) ); } );

	// count the times that *mf == Cm and *(mf+mMach) == or != Cm to choose for swap
	t_time lt = mc? *mq: 0;
	vector < t_time > ::iterator t = p.begin() + st_operation(o);
	t_mach fc = 0;
	{ if ( lt < *(--lm) ) lt = *lm; lt += *t; *(--mf) = *(--me) + ( *(--mq) = lt ); }
	UNFOLDFOR2 ( o - *(--op) + 1 , { if ( lt < *(--lm) ) lt = *lm; lt += *(--t);  if ( Cm == *(--me+mMach) + *mq ) ++fc; *(--mf) = *(me) + ( *(--mq) = lt ); } );

	UNFOLDFOR2 ( mq - _mq + 1 , { *(--mf) = *(--me) + ( *(--mq) = *(--lm) ); } );
	return (fc);
}

inline
void t_solution::__PropagateFi ( const t_operation & opb, const t_operation & ope )
{
	vector < t_time > ::iterator t = p.begin() + st_operation(opb);
	vector < t_time > ::iterator xe = _LM.begin();
	t_time lt;
	t_mach mc = (opb-1) % mMach; // mach [0,m-1]
	if (mc)
	{
		xe += mc;
		lt = *(xe-1);
		if ( lt < *(xe) ) lt = *xe;
		lt += *t;
		*xe = lt;
	}
	else
	{
		*xe += *t;
		lt = *xe;
	}
	UNFOLDFOR2 ( ope - opb + 1, { if ( lt < *(++xe) ) lt = *xe; lt += *(++t); *xe = lt; } );
}

inline
void t_solution::_PropagateFi ( const vector < t_operation > ::iterator & opbegin )
{
	// Fills forward competion times.
	for ( vector < t_operation > ::iterator op = opbegin, _op = ops.end(); op < _op; op+=2 )
		__PropagateFi ( *op, *(op+1) );
	Cm = _LM.back();
}

inline
void t_solution::Evaluate()
{
	vector < t_operation > ::iterator op = ops.begin();
	_LM.assign(t_size_type(mMach), 0);
	_PropagateFi( op );
}

#ifndef NDEBUG
void t_solution::VerifyCm()
{
	t_time _Cm = Cm;
	assert( check_ops_order(ops) );
	Evaluate();
	assert ( _Cm == Cm );
}

void t_solution::Verify()
{
	VerifyCm();
}
#endif

inline
t_time t_solution::CalculateCMs ( const t_operation jo )
{
	vector < t_time > ::iterator to, me0, lm, me1, mq0;

	auto __PropagateMiB0 = [&] ()
	{
		mq0 = lm = Mq0.begin() + st_operation(ops.size()/2+1) * mMach;
		UNFOLDFOR2 ( mMach, { *(--mq0) = 0; } ); { *(--mq0) = 0; }
	};

	auto __PropagateMiB = [&] ( t_operation & op )
	{
		vector < t_time > ::iterator t = p.begin() + st_operation(op);
		t_time lt = *(--mq0) = *(--lm) + *t;
		UNFOLDFOR2 ( mMach, { if ( lt < *(--lm) ) lt = *lm; *(--mq0) = ( lt += *(--t) ); } );
	};

	auto __PropagateMiA0 = [&] ()
	{
		lm = Me0.begin() - 1;
		me0 = lm + mMach;
		me1 = Me1.begin();
		vector < t_time > ::iterator t = to;
		t_time lt = *me1 = *t;
		t_time mxt = *mq0 + *me1;
		UNFOLDFOR2 ( mMach, { t_time cmt = *(++mq0) + ( *(++me1) = ( lt += *(++t) ) ); if ( mxt <= cmt ) mxt = cmt; } );
		return mxt;
	};

	auto __PropagateMiA = [&] ( t_operation & op )
	{
		vector < t_time > ::iterator jt = to;
		vector < t_time > ::iterator t = p.begin() + st_operation(op);
		t_time lt = *(++me0) = *(++lm) + *t;
		t_time llt = *(++me1) = lt + *(jt);
		t_time mxt = *(++mq0) + llt;
		UNFOLDFOR2 ( mMach, { if ( lt < *(++lm) ) lt = *lm; lt += *(++t); *(++me0) = lt; if ( llt < lt ) llt = lt; llt += *(++jt); t_time cmt = *(++mq0) + ( *(++me1) = llt );  if ( mxt <= cmt ) mxt = cmt; } );
		return mxt;
	};

	/////////////////// CalculateCMs begins here ///////////////////
	t_time TFmin = max_time;
	to = p.begin() + st_operation(jo);

	// Fills backward completion time (q)
	{
		__PropagateMiB0 ();
		for ( vector < t_operation > ::iterator op = ops.end()-1, _op = ops.begin() - 1; op > _op; op-=2)
			__PropagateMiB ( *op );
	}

	// Fills forward completion times (e) and inserting (f).
	{
		TFmin = __PropagateMiA0 ();
		ins_bj.resize(1);
		ins_bj.back() = ops.begin();
		for ( vector < t_operation > ::iterator op = ops.begin(), _op = ops.end(); op < _op;)
		{
			t_time mxt = __PropagateMiA ( *op ); op+=2;
			if ( mxt <= TFmin )
			{
				if ( mxt < TFmin )
				{
					TFmin = mxt;
					ins_bj.clear();
				}
				ins_bj.push_back(op);
			}
		}
	}
	std::reverse(ins_bj.begin(),ins_bj.end());
	return TFmin;
}

inline
t_time t_solution::CalculateCMs_NP ( const t_operation jo )
{
	vector < t_time > ::iterator to, lm, me0, me1, mq0, mq1, mc0, mc1;

	auto __PropagateMiA0 = [&] ()
	{
		lm = Me0.begin() - 1;
		me0 = lm + mMach;
		me1 = Me1.begin();
		mc0 = MC0.begin();
		mc1 = MC1.begin();

		vector < t_time > ::iterator t = to;
		t_time lt = *(mc0) = *(me1) = *(t);
		UNFOLDFOR2 ( mMach , { *(++mc0) = *(++me1) = ( lt += *(++t) ); } );

		*(mc1) = 0;
		UNFOLDFOR2 ( mMach , { *(++mc1) = 0; } );
	};

	auto __PropagateMiA = [&] ( vector < t_operation > ::iterator & op )
	{
		t_operation o = *(op);
		t_mach mach = (o-1) % mMach; //adjusted
		vector < t_time > ::iterator _me = me0 + mMach;

		UNFOLDFOR2 ( mach + 1 , { *(++mc1) = *(++me0) = *(++lm); t_time _t = *(++me1-mMach); *(++mc0) = *(me1) = _t; } )

		t_time lt = mach? *me0: 0;
		t_time llt = mach? *me1: 0;
		vector < t_time > ::iterator jt = to + mach;
		vector < t_time > ::iterator t = p.begin() + st_operation(o);

		{ if ( lt < *(++lm) ) lt = *lm; lt += *t; *(++mc1) = *(++me0) = lt; if ( llt < lt ) llt = lt; llt += *(jt); *(++mc0) = *(++me1) = llt; }
		UNFOLDFOR2 ( *(++op) - o + 1 , { if ( lt < *(++lm) ) lt = *lm; lt += *(++t); *(++mc1) = *(++me0) = lt; if ( llt < lt ) llt = lt; llt += *(++jt); *(++mc0) = *(++me1) = llt; } );

	 	UNFOLDFOR2 ( _me - me0 + 1 , { t_time _t = *(++mc1) = *(++me0) = *(++lm); if ( llt < _t ) llt = _t; llt += *(++jt); *(++mc0) = *(++me1) = llt; } );
	};

	auto __PropagateMiB0 = [&] ()
	{
		st_operation delta = mc0 - MC0.begin();
		assert (delta == st_operation((ops.size()/2+1)) * mMach - 1);
		mq0 = Mq0.begin() + delta; lm = mq0 + 1;
		mq1 = Mq1.begin() + delta;
		mc0 -= mMach - 1;

		*(mq0) = 0;
		UNFOLDFOR2 ( mMach , { *(--mq0) = 0; } );

		to += mMach - 1;
		vector < t_time > ::iterator t = to;
		t_time lt = *(mq1) = *(t); *(mc1) += lt;
		UNFOLDFOR2 ( mMach , { *(--mq1) = ( lt += *(--t) ); *(--mc1) += lt; } );
	};

	auto __PropagateMiB = [&] ( vector < t_operation > ::iterator & op )
	{
		t_time mxt = 0;
		t_operation o = *(op);
		t_mach mach = mMach - (o-1) % mMach - 1; // adjusted reversed
		vector < t_time > ::iterator _mq = mq0 - mMach;
		UNFOLDFOR2 ( mach + 1 , { *(--mc0) += ( *(--mq0) = *(--lm) ); if ( mxt <= *mc0 ) mxt = *mc0; t_time _t = *(--mq1 + mMach); *(--mc1) += ( *(mq1) = _t ); } );

		t_time lt = mach? *mq0: 0;
		t_time llt = mach? *mq1: 0;
		vector < t_time > ::iterator jt = to - mach;
		vector < t_time > ::iterator t = p.begin() + st_operation(o);

		{ if ( lt < *(--lm) ) lt = *lm; lt += *t; *(--mc0) += ( *(--mq0) = lt ); if ( mxt <= *mc0 ) mxt = *mc0; if ( llt < lt ) llt = lt; llt += *(jt); *(--mc1) += ( *(--mq1) = llt ); }
		UNFOLDFOR2 ( o - *(--op) + 1 , { if ( lt < *(--lm) ) lt = *lm; lt += *(--t); *(--mc0) += ( *(--mq0) = lt ); if ( mxt <= *mc0 ) mxt = *mc0; if ( llt < lt ) llt = lt; llt += *(--jt); *(--mc1) += ( *(--mq1) = llt ); } );

		UNFOLDFOR2 ( mq0 - _mq + 1 , { t_time _t = *(--mq0) = *(--lm); *(--mc0) += _t; if ( mxt <= *mc0 ) mxt = *mc0; if ( llt < _t ) llt = _t; llt += *(--jt); *(--mc1) += ( *(--mq1) = llt ); } );

		return mxt;
	};

	auto __PropagateM_LxXxR = [&] ( )
	{
		// LeABq
		t_time ltl = *mc1;
		{ if (ltl < *(++mc1)) ltl = *(mc1); *(lm) = ltl; }
		UNFOLDFOR2 ( mMach - 3 , { if (ltl < *(++mc1)) ltl = *(mc1); *(++lm) = ltl; } );
		{ if (ltl < *(++mc1)) ltl = *(mc1); if (ltl < *(++mc1)) ltl = *(mc1); }

		// eBAqR
		t_time lt = *(mc0);
		{ if (lt < *(--mc0)) lt = *mc0; if (*(lm) < lt) *lm = lt; mc1 = lm;}
		UNFOLDFOR2 ( mMach - 3 , { if (lt < *(--mc0)) lt = *mc0; if (*(--lm) < lt) *lm = lt; if (*mc1 > *lm) mc1 = lm; } );
		{ if (lt < *(--mc0)) lt = *mc0; if (lt < *(--mc0)) lt = *mc0; }
		return ( ltl < lt )? ltl: lt;
	};

	/////////////////// CalculateCMs begins here ///////////////////
	t_time TFmin;
	to = p.begin() + st_operation(jo);
	{
		__PropagateMiA0 ();
		for ( vector < t_operation > ::iterator op = ops.begin(), _op = ops.end(); op < _op; ++op)
			__PropagateMiA ( op );
		TFmin = *(me1);
	}
	ins_bj.resize(1);
	ins_xp.resize(1);
	ins_bj.back() = ops.end(); // means after all jobs
	ins_xp.back() = 0;

	// Fills backward completion time (q),  (M) over (f), and Mi
	{
		__PropagateMiB0 ();
		for ( vector < t_operation > ::iterator op = ops.end()-1, _op = ops.begin(); op > _op; --op)
		{
			t_time mxt = __PropagateMiB ( op );
			if ( mxt <= TFmin )
			{
				if ( mxt < TFmin )
				{
					TFmin = mxt;
					ins_bj.clear();
					ins_xp.clear();
				}
				ins_bj.push_back(op);
				ins_xp.push_back(0);
			}
		}
	}

	///////////////////  Evaluate non-permutation insertions ///////////////////
	static vector< vector < t_time > ::iterator > mnm;
	static vector < t_time > EQ, MX;
	mnm.reserve(t_size_type(mMach-3));
	EQ.resize(t_size_type(mMach-3));
	MX.resize(t_size_type(mMach-3));

	st_operation delta = st_operation((ops.size()/2 + 1)) * mMach;
	for ( vector < t_operation > ::iterator cop = ops.end(), _cop = ops.begin(); cop > _cop; )
	{
		delta -= mMach;
		t_operation oe = *(--cop);
		t_operation ob = *(--cop);

		// skip if less than 3 ops
		if ( ob + 1 >= oe ) continue;

		mc0 = MC0.begin() + delta - 1;
		mc1 = MC1.begin() + delta;
		lm = MX.begin();
		t_time mnmx = __PropagateM_LxXxR ();
		if ( *mc1 < mnmx )
		{
			t_time lt;
			if ( *mc1 > TFmin ) continue;
			{
				t_mach m_o = (ob - 1) % mMach;
				if ( m_o == 0 ) ++m_o;

				lm = MX.begin() + m_o - 1;
				me1 = Me1.begin() + delta + m_o;
				mq1 = Mq1.begin() + delta - mMach + m_o + 1;

				t_mach m_e = (oe - 2) % mMach + 3;
				if ( m_e > mMach ) m_e = mMach;
				m_e -= 3;

				{ t_time _t = *(me1) + *(mq1); if ( _t > *(lm) ) *lm = _t; mnm.clear (); mnm.push_back(lm); }
				lt = *lm;
				UNFOLDFOR2 ( m_e - m_o  + 1 , { t_time _t = *(++me1) + *(++mq1); if ( _t > *(++lm) ) *lm = _t; if (lt > *lm) { lt = *lm; mnm.clear(); mnm.push_back(lm); } else if ( lt == *lm) mnm.push_back(lm); } );
			}

			if ( lt > TFmin ) continue;
			{
				if ( lt < TFmin )
				{
					TFmin = lt;
					ins_bj.clear();
					ins_xp.clear();
					for ( vector< vector < t_time > ::iterator >::iterator m = mnm.end()-1, _m = mnm.begin(); m >=_m; --m )
					{
						ins_bj.push_back(cop);
						ins_xp.push_back(*m - MX.end() - 1); //split operations in this machine
					}
				}
				else if (ins_xp.back()) {
					for ( vector< vector < t_time > ::iterator >::iterator m = mnm.end()-1, _m = mnm.begin(); m >=_m; --m )
					{
						ins_bj.push_back(cop);
						ins_xp.push_back(*m - MX.end() - 1); //split operations in this machine
					}
				}
			}
			continue;
		}
		mc0 = MC1.begin() + delta + mMach - 1;
		mc1 = MC0.begin() + delta - mMach;
		lm = MX.begin();
		t_time mnmz = __PropagateM_LxXxR ();
		if ( *mc1 >= mnmz ) continue;
		{
			if ( *mc1 > TFmin ) continue;
			t_mach m_e = (oe - 1) % mMach;
			{
				vector < t_time > ::iterator t = p.begin() + st_operation(oe);
				mq1 = Mq1.begin() + delta + m_e; --m_e;
				t_time lt = *mq1;

				m_e += 3;
				if ( m_e > mMach)
				{
					m_e = mMach;
					lt += *t; --t;
					if ( lt < *(--mq1) ) lt = *mq1;
				}
				m_e -= 3;
				mq0 = EQ.begin() + m_e - 1;

				t_mach m_o = (ob - 1) % mMach;
				if ( m_o == 0 ) ++m_o;

				{ lt += *(t); *(mq0) = lt; }
				UNFOLDFOR2 ( m_e - m_o + 1 , { if ( lt < *(--mq1) ) lt = *mq1; lt += *(--t); *(--mq0) = lt; } );
			}

			t_time lt;
			{
				vector < t_time > ::iterator t = p.begin() + st_operation(ob);
				t_mach m_o = (ob - 1) % mMach;
				me1 = Me1.begin() + delta - mMach + m_o;
				t_time lf = *me1;
				if ( m_o == 0 )
				{
					++m_o;
					lf += *t; ++t;
					if ( lf < *(++me1) ) lf = *me1;
				}
				assert ( mq0 == EQ.begin() + m_o - 1 );
				lm = MX.begin() + m_o - 1;

				{ lf += *(t); t_time _t = *(mq0) + lf; if ( _t > *(lm) ) *lm = _t; mnm.clear (); mnm.push_back(lm);}
				lt = *lm;
				UNFOLDFOR2 ( m_e - m_o + 1 , { if ( lf < *(++me1) ) lf = *me1; lf += *(++t); t_time _t = *(++mq0) + lf; if ( _t > *(++lm) ) *lm = _t; if (lt > *lm) { lt = *lm; mnm.clear(); mnm.push_back(lm); } else if ( lt == *lm) mnm.push_back(lm); } );
			}

			if ( lt > TFmin ) continue;
			{
				if ( lt < TFmin )
				{
					TFmin = lt;
					ins_bj.clear();
					ins_xp.clear();
					for ( vector< vector < t_time > ::iterator >::iterator m = mnm.end()-1, _m = mnm.begin(); m >=_m; --m )
					{
						ins_bj.push_back(cop);
						ins_xp.push_back(*m - MX.begin() + 2); // split operations in this machine
					}
				}
				else if (ins_xp.back())
				{
					for ( vector< vector < t_time > ::iterator >::iterator m = mnm.end()-1, _m = mnm.begin(); m >=_m; --m )
					{
						ins_bj.push_back(cop);
						ins_xp.push_back(*m - MX.begin() + 2); // split operations in this machine
					}
				}
			}
			continue;
		}
	}
	return TFmin;
}

inline
vector < t_operation > ::iterator t_solution::CalculateBJ( const t_operation jo )
{
	if ( ins_bj.size() == 1 ) return ins_bj.front();
	double mit = std::numeric_limits<double>::max();
	vector < t_operation > ::iterator bj;

	for ( vector < t_operation > ::iterator & cj : ins_bj )
	{
		double cit = 0.0;
		double ddd;
		st_operation df = ( cj - ops.begin() ) * mMach / 2;
		t_operation op = *(cj);
		vector < t_time > ::iterator
			ti = p.begin() + jo,
			tp = p.begin() + *(cj),
			me = Me0.begin() + df + mMach,
			mf = Me1.begin() + df;
		if ( cj < ops.end() - 1 )
		{
			t_time lf = *mf + *tp;
			UNFOLDFOR2 ( mMach, { st_operation tcit = st_operation ( *(++mf) + *(++tp) ) - st_operation ( *(++me) ) - st_operation ( *(++ti) ); if (lf > *mf) tcit += st_operation(lf) - st_operation(*mf); else lf = *mf; lf += *tp; ddd = double(tcit); ddd /= double(nJobs); ddd*=(nJobs-t_job(ops.size()/2)-1); cit += ddd; } );
		}
		else
		{
			me-=mMach;
			UNFOLDFOR2 ( mMach, { ddd = double (*(++mf) - *(++me) - *(++ti)); ddd /= double(nJobs); ddd *= (nJobs-t_job(ops.size()/2)-1); cit += ddd; } );
		}
		if ( cit <= mit )
		{
			mit = cit;
			bj = cj;
		}
	}
	return bj;
}

inline
t_time t_solution::CalculateCMs_LJP ( const t_operation jo )
{
	vector < t_time > ::iterator to, me0, lm, me1, mq0;
	t_time TFmin = max_time;

	auto __PropagateMiB0 = [&] ()
	{
		mq0 = lm = Mq0.begin() + st_operation(ops.size()/2+1) * mMach;
		UNFOLDFOR2 ( mMach, { *(--mq0) = 0; } ); { *(--mq0) = 0; }
	};

	auto __PropagateMiB = [&] ( t_operation & op )
	{
		vector < t_time > ::iterator t = p.begin() + st_operation(op);
		t_time lt = *(--mq0) = *(--lm) + *t;
		UNFOLDFOR2 ( mMach, { if ( lt < *(--lm) ) lt = *lm; *(--mq0) = ( lt += *(--t) ); } );
	};

	auto __PropagateMiA0 = [&] ()
	{
		lm = Me0.begin() - 1;
		me0 = lm + mMach;
		me1 = Me1.begin();
		vector < t_time > ::iterator t = to;
		_LM.resize(t_size_type(mMach));
		vector < t_time > ::iterator ff = _LM.begin();
		t_time lt = *ff = *me1 = *t;
		t_time mxt = *mq0 + *me1;
		UNFOLDFOR2 ( mMach, { t_time cmt = *(++mq0) + ( *(++ff) = *(++me1) = ( lt += *(++t) ) ); if ( mxt <= cmt ) mxt = cmt; } );
		return mxt;
	};

	auto __PropagateMiA = [&] ( t_operation & op )
	{
		vector < t_time > ::iterator jt = to;
		vector < t_time > ::iterator t = p.begin() + st_operation(op);
		t_time lt = *(++me0) = *(++lm) + *t;
		t_time llt = *(++me1) = lt + *(jt);
		t_time mxt = *(++mq0) + llt;
		UNFOLDFOR2 ( mMach, { if ( lt < *(++lm) ) lt = *lm; lt += *(++t); *(++me0) = lt; if ( llt < lt ) llt = lt; llt += *(++jt); t_time cmt = *(++mq0) + ( *(++me1) = llt );  if ( mxt <= cmt ) mxt = cmt; } );
		return mxt;
	};

	auto __CalculatePriority = [&] ( vector < t_time > ::iterator ff )
	{
		vector < double > G; G.resize(t_size_type(mMach));
		vector < uint_fast16_t > W; W.resize(t_size_type(mMach));
		vector < t_time > ::iterator cq = mq0 - mMach + 1;
		vector < t_time > ::iterator cf = ff;
		vector < double > ::iterator cg = G.begin();
		double ag = *cg = double (TFmin - *cf - *cq);
		UNFOLDFOR2 ( mMach, { ag += ( *(++cg) = double ( TFmin - *(++cf) - *(++cq) ) ); } );
		{
			vector < uint_fast16_t > O; O.resize(t_size_type(mMach));
			iota(O.begin(),O.end(),0);
			std::stable_sort( O.begin(), O.end(),
				[&G](const uint_fast16_t & i, const uint_fast16_t & j) { return (G[i]>G[j] ||(G[i]==G[j] && i>j)); } );
			for ( uint_fast8_t i = 0 ; i < uint_fast8_t(mMach); ++i ) W[O[i]] = i;
		}
		cf = ff;
		cg = G.begin();
		auto cw = W.begin();
		ag /= mMach;
		t_time ttt = (*cf) * (*cw);
		double ttmf = ( (*cg > ag) ? *cg - ag : ag - *cg );
		UNFOLDFOR2 ( mMach, { ttt += *(++cf) * *(++cw); ttmf += ((*(++cg) > ag) ? *cg - ag : ag - *cg) ; } );
		ttmf = double(ttt) + 3.4 * ttmf / double(mMach);

		cq = mq0 - mMach + 1;
		cf = _LM.begin();
		cg = G.begin();
		ag = *cg = double (TFmin - *cf - *cq);
		UNFOLDFOR2 ( mMach, { ag += ( *(++cg) = double ( TFmin - *(++cf) - *(++cq) ) ); } );
		cf = _LM.begin();
		cg = G.begin();
		cw = W.begin();
		ag /= mMach;
		ttt = (*cf) * (*cw);
		double ttff = ( (*cg > ag) ? *cg - ag : ag - *cg );
		UNFOLDFOR2 ( mMach, { ttt += *(++cf) * *(++cw); ttff += ((*(++cg) > ag) ? *cg - ag : ag - *cg) ; } );
		ttff = double(ttt) + 3.4 * ttff / double(mMach);

		return ( ttmf < ttff );
	};

	/////////////////// CalculateCMs begins here ///////////////////
	TFmin = max_time;
	to = p.begin() + st_operation(jo);

	// Fills backward completion time (q)
	{
		__PropagateMiB0 ();
		for ( vector < t_operation > ::iterator op = ops.end()-1, _op = ops.begin() - 1; op > _op; op-=2)
			__PropagateMiB ( *op );
	}

	// Fills forward completion times (e) and inserting (f).
	{
		TFmin = __PropagateMiA0 ();
		ins_bj.resize(1);
		ins_bj.back() = ops.begin();
		for ( vector < t_operation > ::iterator op = ops.begin(), _op = ops.end(); op < _op;)
		{
			t_time mxt = __PropagateMiA ( *op ); op+=2;
			if ( mxt < TFmin )
			{
				TFmin = mxt;
				ins_bj.back() = (op);
				std::copy ( me1-mMach+1, me1+1, _LM.begin() ); // copy last F into LM;
			}
			else// ( mxt >= TFmin )
			{
				// Calculate F'' in LM
				vector < t_time > ::iterator ff = _LM.begin();
				vector < t_time > ::iterator t = p.begin() + *(op-2);
				t_time lt = ( *(ff) += *t );
				UNFOLDFOR2 ( mMach, { if ( lt < *(++ff) ) lt = *ff; lt += *(++t); *(ff) = lt; } );
				if ( mxt == TFmin )
				{
					// Calculate p for F and F''
					if ( __CalculatePriority ( me1 - mMach + 1 ) )
					{
						ins_bj.back() = (op);
						std::copy ( me1-mMach+1, me1+1, _LM.begin() ); // copy last F into LM;
					}
				}
			}
		}
	}
	return TFmin;
}

template < const bool RandomInsertion = true >
inline
void t_solution::InsertJobOp ( const t_operation jo )
{
	Cm = CalculateCMs ( jo );
	t_operation _jo = jo + mMach - 1;
	vector < vector < t_operation > ::iterator > ::iterator bj;
	if ( RandomInsertion ) bj = ins_bj.begin() + rand()%st_operation(ins_bj.size());
	else bj = ins_bj.end() - 1;
	// insert before a block or after all operations
	ops.insert ( *bj, { jo , _jo } );
	#ifndef NDEBUG
	assert( check_ops_order(ops) );
	VerifyCm();
	#endif
}

template < bool RandomInsertion = true >
inline
void t_solution::InsertJobOp_NP ( const t_operation jo )
{
	#ifndef NDEBUG
	auto lop = ops;
	#endif
	Cm = CalculateCMs_NP ( jo );
	t_operation _jo = jo + mMach - 1;
	assert ( INT_FAST16_MAX > ins_bj.size() );
	t_size_type dp = ( RandomInsertion )? t_size_type(rand())%ins_bj.size(): (ins_bj.size()-1);
	vector < t_operation > ::iterator bj = ins_bj[dp];
	int_fast8_t xp = ins_xp[dp];
	if ( xp == 0 )
	{
		// insert before a block or after all operations
		ops.insert ( bj, { jo , _jo } );
	}
	else if ( xp > 0 )
	{
		//if ( cross > 1 ) mn - MX.begin() + 2;
		// split this job arround an already scheduled job
		t_operation ob = *bj;
		*(bj++) = jo;
		t_operation oe = *bj;
		t_operation no = jo + t_operation(xp);
		*(bj++) = no - 1;
		ops.insert ( bj, { ob, oe, no, _jo } );
	}
	else
	{
		//if (cross == 1) lm - MX.end() - 1;
		// insert this job splitting an already scheduled job
		t_operation tb = *bj - *bj%mMach + mMach - t_operation(-xp); // xp is negative
		ops.insert ( ++bj, {tb, jo, _jo, tb + 1 } );
	}
	if (_max_swap_size < ops.size()) _max_swap_size = ops.size();
	#ifndef NDEBUG
	assert( check_ops_order(ops) );
	VerifyCm();
	#endif
}

inline
void t_solution::InsertJobOpFF ( const t_operation jo )
{
	Cm = CalculateCMs ( jo );
	t_operation _jo = jo + mMach - 1;
	vector < t_operation > ::iterator bj = CalculateBJ(jo);
	ops.insert ( bj, { jo , _jo } );
	#ifndef NDEBUG
	assert( check_ops_order(ops) );
	VerifyCm();
	#endif
}

inline
void t_solution::InsertJobOpFF_NP ( const t_operation jo )
{
	#ifndef NDEBUG
	auto lop = ops;
	#endif
	Cm = CalculateCMs_NP ( jo );
	t_operation _jo = jo + mMach - 1;
	assert ( INT_FAST16_MAX > ins_bj.size() );
	t_size_type dp = (ins_bj.size()-1);
	vector < t_operation > ::iterator bj = ins_bj[dp];
	int_fast8_t xp = ins_xp[dp];
	if ( xp == 0 )
	{
		// insert before a block or after all operations
		bj = CalculateBJ(jo);
		ops.insert ( bj, { jo , _jo } );
	}
	else if ( xp > 0 )
	{
		//if ( cross > 1 ) mn - MX.begin() + 2;
		// split this job arround an already scheduled job
		t_operation ob = *bj;
		*(bj++) = jo;
		t_operation oe = *bj;
		t_operation no = jo + t_operation(xp);
		*(bj++) = no - 1;
		ops.insert ( bj, { ob, oe, no, _jo } );
	}
	else
	{
		//if (cross == 1) lm - MX.end() - 1;
		// insert this job splitting an already scheduled job
		t_operation tb = *bj - *bj%mMach + mMach - t_operation(-xp); // xp is negative
		ops.insert ( ++bj, {tb, jo, _jo, tb + 1 } );
	}
	if (_max_swap_size < ops.size()) _max_swap_size = ops.size();
	#ifndef NDEBUG
	assert( check_ops_order(ops) );
	VerifyCm();
	#endif
}

inline
void t_solution::InsertJobOpLJP ( const t_operation jo )
{
	Cm = CalculateCMs_LJP ( jo );
	t_operation _jo = jo + mMach - 1;
	vector < t_operation > ::iterator bj = ins_bj.back();
	ops.insert ( bj, { jo , _jo } );
	#ifndef NDEBUG
	VerifyCm();
	#endif
}

inline
void t_solution::DeleteJob( const t_job j )
{
	t_operation jo = j * mMach + 1;
	t_operation _jo = jo + mMach - 1;

	vector < t_operation > ::iterator vt = ops.begin();
	for (vector < t_operation > ::iterator _t = ops.end(); vt < _t; vt+=2 )
		if ( jo <= *vt && *vt <= _jo ) break;

	t_operation lj = nJobs;
	st_operation d = 2;
	if ( vt > ops.begin() )
	{
		vector < t_job > :: iterator lv = vt - 1;
		lj = ( ( *lv - 1 ) / mMach );
		if ( vt+2 < ops.end() )
			if ( ( *(vt+2) - 1 ) / mMach == lj )
			{
				*lv = *(vt+3);
				d += 2;
			}
	}
	vector < t_operation > ::iterator xt = vt + d;
	if ( *(vt+1) < _jo )
	{
		for (vector < t_operation > ::iterator _t = ops.end(); xt < _t; )
		{
			if ( jo <= *xt && *xt <= _jo )
			{
				xt+=2;
				if ( xt < _t )
					if ( ( *xt - 1 ) / mMach == lj )
					{
						*(vt-1) = *(++xt);
						++xt;
					}
				if ( *(vt+1) == _jo ) break;
			}
			else
			{
				*vt = *xt;
				*(++vt) = *(++xt);
				lj = ( *vt - 1 ) / mMach;
				++vt; ++xt;
			}
		}
	}
	for (vector < t_operation > ::iterator _t = ops.end(); xt < _t; )
	{
		*vt = *xt;
		++vt; ++xt;
	}
	ops.resize(t_size_type(vt - ops.begin()));
	assert( check_ops_order(ops) );
}


inline
void t_solution::Delete2Jobs( const t_operation j0,  const t_operation j1 )
{
	vector < t_operation > ::iterator vt = ops.begin();
	for (vector < t_operation > ::iterator _t = ops.end(); vt < _t; vt+=2 )
	{
		t_job t = (*vt-1)/mMach;
		if ( t == j0 ) break;
		if ( t == j1 ) break;
	}
	t_operation lj = nJobs;
	st_operation d = 2;
	if ( vt > ops.begin() )
	{
		lj = ( ( *(vt - 1) - 1 ) / mMach );
		if ( vt+2 < ops.end() )
			if ( ( *(vt+2) - 1 ) / mMach == lj )
			{
				*(vt-1) = *(vt+3);
				d += 2;
			}
	}
	for (vector < t_operation > ::iterator xt = vt + d, _t = ops.end(); xt < _t; )
	{
		t_job t = (*xt-1)/mMach;
		if ( t == j0 || t == j1 )
		{
			xt+=2;
			if ( xt < _t )
				if ( ( *xt - 1 ) / mMach == lj )
				{
					*(vt-1) = *(++xt);
					++xt;
				}
		}
		else
		{
			*vt = *xt;
			*(++vt) = *(++xt);
			lj = ( *vt - 1 ) / mMach;
			++vt; ++xt;
		}
	}
	ops.resize(t_size_type(vt - ops.begin()));
	assert( check_ops_order(ops) );
}

inline
void t_solution::DeleteJobs( const vector < t_operation > :: iterator & bj,  const vector < t_operation > :: iterator & ej )
{
	vector < t_operation > ::iterator vt = ops.begin();
	for (vector < t_operation > ::iterator _t = ops.end(); vt < _t; vt+=2 )
	{
		t_job t = (*vt-1)/mMach;
		for(vector < t_job > :: iterator cj = bj; cj < ej; ++cj) if ( t == *cj ) goto DeleteJobs_FirstFound;
	}
	DeleteJobs_FirstFound:
	t_operation lj = nJobs;
	st_operation d = 2;
	if ( vt > ops.begin() )
	{
		vector < t_job > :: iterator lv = vt - 1;
		lj = ( ( *lv - 1 ) / mMach );
		if ( vt+2 < ops.end() )
			if ( ( *(vt+2) - 1 ) / mMach == lj )
			{
				*lv = *(vt+3);
				d += 2;
			}
	}
	for (vector < t_operation > ::iterator xt = vt + d, _t = ops.end(); xt < _t; )
	{
		vector < t_job > :: iterator cj = bj;
		t_job t = (*xt-1)/mMach;
		for(; cj < ej; ++cj) if ( t == *cj ) goto DeleteJobs_AnotherFound;
		//if ( cj >= ej ) after last for then
		{
			*vt = *xt;
			*(++vt) = *(++xt);
			lj = ( *vt - 1 ) / mMach;
			++vt; ++xt;
			continue;
		}
		//else if ( cj < ej ), for jumps here
		{
			DeleteJobs_AnotherFound:
			xt+=2;
			if ( xt < _t )
				if ( ( *xt - 1 ) / mMach == lj )
				{
					*(vt-1) = *++xt;
					++xt;
				}
		}
	}
	ops.resize(t_size_type(vt - ops.begin()));
	assert( check_ops_order(ops) );
}


////////////////////////////////////////////////////////////
// Local Search Heuristics

template < t_solution::_t_InsertJob _InsertJob >
inline
void t_solution::LocalSearch_Insertion()
{
	static vector < t_operation > bo;
	bo.reserve(t_size_type(3*nJobs));
	bo = ops;
	t_time bCm;
	bCm = Cm;
	t_time _ls_iters = 0;
	for (vector < t_job > ::iterator lj = jobs.end();;)
	{
		++_ls_iters;
		for ( vector < t_job > ::iterator j = jobs.begin(), _j = lj; j < _j; ++j )
		{
			DeleteJob ( *j );
			(this->*_InsertJob) ( t_operation ( *j ) * mMach + 1 );
			#ifndef NDEBUG
			VerifyCm();
			#endif
			if ( Cm < bCm )
			{
				bCm = Cm;
				bo = ops;
				lj = j;
				goto LocalSearch_Insertion_Cm_IMPROVED;
			}
			else
			{
				Cm = bCm;
				ops = bo;
			}
		}

		break;
		LocalSearch_Insertion_Cm_IMPROVED:

		for ( vector < t_job > ::iterator j = lj+1, _j = jobs.end(); j < _j; ++j )
		{
			DeleteJob ( *j );
			(this->*_InsertJob) ( t_operation ( *j ) * mMach + 1 );
			#ifndef NDEBUG
			VerifyCm();
			#endif
			if ( Cm < bCm )
			{
				bCm = Cm;
				bo = ops;
				lj = j;
			}
			else
			{
				Cm = bCm;
				ops = bo;
			}
		}
	}
	if ( _max_ls_iters < _ls_iters ) _max_ls_iters = _ls_iters;
	_tot_ls_iters += _ls_iters;
	#ifndef NDEBUG
	VerifyCm();
	#endif
}

template < t_solution::_t_InsertJob _InsertJob >
inline
void t_solution::PairSearch_Insertion()
{
	static vector < t_operation > bo;
	bo.reserve(t_size_type(3*nJobs));
	jobs.resize(ops.size()/2);
	{
		vector < t_job > ::iterator lj = jobs.begin();
		for ( vector < t_operation > ::iterator op = ops.begin(), _op = ops.end(); op < _op; op+=2, ++lj)
		*lj = (*op)/mMach;
	}

	bo = ops;
	t_time bCm;
	bCm = Cm;
	for (vector < t_job > ::iterator bj = jobs.begin(); bj < jobs.begin()+2; ++bj)
	{// first 0:odds then 1:evens
		for ( vector < t_job > ::iterator j = bj, _j = ( jobs.end() - 1 ); j < _j; j+=2 )
		{//each pair
			Delete2Jobs ( *j, *(j+1) );
			(this->*_InsertJob) ( t_operation ( *j ) * mMach + 1 );
			(this->*_InsertJob) ( t_operation ( *(j+1) ) * mMach + 1 );
			#ifndef NDEBUG
			VerifyCm();
			#endif
			if ( Cm < bCm )
			{
				bCm = Cm;
				bo = ops;
			}
			else
			{
				Cm = bCm;
				ops = bo;
			}
		}
	}
}

template < t_solution::_t_InsertJob _InsertJob, bool RandomInsertion = true >
inline
void t_solution::LocalSearch_PRInsertionAll()
{
	vector < t_time > ::iterator me, lm, mf, mq;
	static vector < std::pair < t_job, t_job > > nbs, nbc;
	nbs.reserve(ops.size());
	nbc.reserve(ops.size());

	auto UpdateNBS = [&] ()
	{
		nbs.clear();
		nbc.clear();
		t_job  jll = (ops.front())/mMach;
		for ( vector < t_operation > ::iterator op = ops.begin() + 2, _op = ops.end(); op < _op; op+=2 )
		{
			t_job jl = *op/mMach;
			nbs.push_back(std::make_pair(jll,jl));
			nbc.swap(nbs);
			jll = jl;
		}

		if ( nbs.size() < nbc.size() ) nbc.swap(nbs);
		nbs.reserve(nbs.size()+nbc.size());
		nbs.insert(nbs.end(),nbc.begin(),nbc.end());

		if ( RandomInsertion )
			std::random_shuffle(nbs.begin(),nbs.end());
	};

	static vector < t_operation > bo;
	bo.reserve(t_size_type(3*nJobs));
	bo = ops;
	t_time _ls_iters = 0;
	for(t_time oCm = max_time, bCm = Cm; oCm > Cm;)
	{
		++_ls_iters;
		oCm = Cm;
		UpdateNBS();
		for ( vector < std::pair < t_job, t_job > > ::iterator pj = nbs.begin(), _pj = nbs.end(); pj < _pj; ++pj)
		{
			Delete2Jobs ( (*pj).first, (*pj).second );
			(this->*_InsertJob) ( t_operation ( (*pj).first ) * mMach + 1 );
			(this->*_InsertJob) ( t_operation ( (*pj).second ) * mMach + 1 );
			#ifndef NDEBUG
			VerifyCm();
			#endif
			if ( Cm < bCm )
			{
				bCm = Cm;
				bo = ops;
			}
			else
			{
				Cm = bCm;
				ops = bo;
			}
		}
	}
	if ( _max_ls_iters < _ls_iters ) _max_ls_iters = _ls_iters;
	_tot_ls_iters += _ls_iters;
}

template < t_solution::_t_InsertJob _InsertJob, bool RandomInsertion = true >
inline
void t_solution::LocalSearch_PRInsertionCrt()
{
	vector < t_time > ::iterator me, lm, mf, mq;
	static vector < std::pair < t_job, t_job > > nbs, nbc;
	nbs.reserve(ops.size());
	nbc.reserve(ops.size());

	auto UpdateNBS = [&] ()
	{
		__PropagateMF0 ( me, lm );
		for ( vector < t_operation > ::iterator op = ops.begin(), _op = ops.end(); op < _op; ++op)
			__PropagateMF ( op, me, lm );
		assert ( Cm == *(me) );

		nbs.clear();
		nbc.clear();

		__PropagateMB0 ( me, lm, mf, mq );
		t_mach fi, fl;
		{ vector < t_operation > ::iterator op = ops.end() - 1; fl = __PropagateMB ( op, me, lm, mf, mq ); }
		for ( vector < t_operation > ::iterator op = ops.end() - 3, _op = ops.begin(); op > _op; --op)
		{
			fi = __PropagateMB ( op, me, lm, mf, mq );
			if ( fl || fi )
			{
				nbs.push_back ( std::make_pair ( *(op)/mMach, *(op+2)/mMach ) );
				nbc.swap(nbs);
			}
			fl = fi;
		}

		nbs.reserve(nbs.size()+nbc.size());
		nbs.insert(nbs.end(),nbc.begin(),nbc.end());

		if ( RandomInsertion )
			std::random_shuffle(nbs.begin(),nbs.end());
	};

	static vector < t_operation > bo;
	bo.reserve(t_size_type(3*nJobs));
	bo = ops;
	t_time _ls_iters = 0;
	for(t_time oCm = max_time, bCm = Cm; oCm > Cm;)
	{
		++_ls_iters;
		oCm = Cm;
		UpdateNBS();
		for ( vector < std::pair < t_job, t_job > > ::iterator pj = nbs.end()-1, _pj = nbs.begin()-1; pj > _pj; --pj)
		{
			Delete2Jobs ( (*pj).first, (*pj).second );
			(this->*_InsertJob) ( t_operation ( (*pj).first ) * mMach + 1 );
			(this->*_InsertJob) ( t_operation ( (*pj).second ) * mMach + 1 );
			#ifndef NDEBUG
			VerifyCm();
			#endif
			if ( Cm < bCm )
			{
				bCm = Cm;
				bo = ops;
			}
			else
			{
				Cm = bCm;
				ops = bo;
			}
		}
	}
	if ( _max_ls_iters < _ls_iters ) _max_ls_iters = _ls_iters;
	_tot_ls_iters += _ls_iters;
}

inline
void t_solution::LocalSearch_fastN5_Cm_NP()
{
	vector < t_time > ::iterator me, lm, mf, mq;

	auto __PropagateMFf = [&] ( vector < t_operation > ::iterator op )
	{
		// needs me, lm defined
		t_operation o = *(op);
		t_mach mc = (o-1) % mMach; //adjusted
		vector < t_time > ::iterator _me = me + mMach;

		UNFOLDFOR2 ( mc + 1 , { *(++me) = *(++lm); } );

		t_time lt = mc? *me: 0;
		vector < t_time > ::iterator t = p.begin() + st_operation(o);

		{ if ( lt < *(++lm) ) lt = *lm; lt += *t; *(++me) = lt; }
		UNFOLDFOR2 ( *(++op) - o + 1 , { if ( lt < *(++lm) ) lt = *lm; lt += *(++t); *(++me) = lt; } );

		UNFOLDFOR2 ( _me - me + 1 , { if ( lt < *(++lm) ) lt = *lm; *(++me) = lt; } );
	};

	auto __PropagateMFs = [&] ( vector < t_operation > ::iterator op )
	{
		// needs me defined
		t_operation o = *(op);
		t_mach mc = (o-1) % mMach; //adjusted
		vector < t_time > ::iterator _me = me + mMach;

		me += mc;
		t_time lt = mc? *me: 0;
		vector < t_time > ::iterator t = p.begin() + st_operation(o);

		{ if ( lt < *(++me) ) lt = *me; lt += *t; *me = lt; }
		UNFOLDFOR2 ( *(++op) - o + 1 , { if ( lt < *(++me) ) lt = *me; lt += *(++t); *me = lt; } );

		UNFOLDFOR2 ( _me - me + 1 , { if ( lt < *(++lm) ) break; *me = lt; } );
	};

	auto __PropagateMBf = [&] ( vector < t_operation > ::iterator op )
	{
		// needs me, mq, lm, mf defined
		t_operation o = *(op);
		t_mach mc = mMach - (o-1) % mMach - 1; // adjusted reversed
		vector < t_time > ::iterator _mq = mq - mMach;

		UNFOLDFOR2 ( mc + 1 , { *(--mf) = *(--me) + ( *(--mq) = *(--lm) ); } );

		t_time lt = mc? *mq: 0;
		vector < t_time > ::iterator t = p.begin() + st_operation(o);
		{ if ( lt < *(--lm) ) lt = *lm; lt += *t; *(--mf) = *(--me) + ( *(--mq) = lt ); }
		UNFOLDFOR2 ( o - *(--op) + 1 , { if ( lt < *(--lm) ) lt = *lm; lt += *(--t); *(--mf) = *(--me) + ( *(--mq) = lt ); } );

		UNFOLDFOR2 ( mq - _mq + 1 , { if ( lt < *(--lm) ) lt = *lm; *(--mf) = *(--me) + ( *(--mq) = lt ); } );
	};

	auto __PropagateMBs = [&] ( vector < t_operation > ::iterator op )
	{
		// needs me, mq, lm, mf defined
		t_operation o = *(op);
		t_mach mc = mMach - (o-1) % mMach - 1; // adjusted reversed
		vector < t_time > ::iterator _mq = mq - mMach;

		mq -= mc;
		t_time lt = mc? *mq: 0;
		vector < t_time > ::iterator t = p.begin() + st_operation(o);
		{ if ( lt < *(--mq) ) lt = *mq; lt += *t; *mq = lt; }
		UNFOLDFOR2 ( o - *(--op) + 1 , { if ( lt < *(--mq) ) lt = *mq; lt += *(--t); *mq = lt; } );

		UNFOLDFOR2 ( mq - _mq + 1 , { if ( lt < *(--lm) ) break; *mq = lt; } );
	};

	vector < t_time > eAB, eBA, qAB, qBA, MAB, MBA, MLR;
	eAB.resize(t_size_type(mMach));
	eBA.resize(t_size_type(mMach));
	qAB.resize(t_size_type(mMach));
	qBA.resize(t_size_type(mMach));
	MAB.resize(t_size_type(mMach));
	MBA.resize(t_size_type(mMach));
	MLR.resize(t_size_type(mMach-3));

	auto __PropagateMLR = [&] ()
	{
		t_time lt = *(me);
		vector < t_time > ::iterator mm = MLR.begin();
		{ if (lt < *(++me)) lt = *me; *(mm) = lt;  }
		UNFOLDFOR2 ( mMach - 3 , { if (lt < *(++me)) lt = *me; *(++mm) = lt; } );

		lm = mm;
		lt = *mq;
		{ if (lt < *(--mq)) lt = *mq; if (*(mm) < lt) *mm = lt; }
		UNFOLDFOR2 ( mMach - 3 , { if (lt < *(--mq)) lt = *mq; if (*(--mm) < lt) *mm = lt; if (*lm > *mm) lm = mm; } );
		{ if (lt < *(--mq)) lt = *mq;  if (lt < *(--mq)) lt = *mq; }
		return lt;
	};

	auto __PropagateMLxXxR = [&] ( t_mach times )
	{
		{ t_time lt = *(mq) + *(me); if ( *(mf) < lt ) *mf = lt; }
		// times in [0, mMach-4] - [0, *] or 0 to mMach - 4
		UNFOLDFOR2 ( times + 1 , { t_time lt = *(--mq) + *(--me); if ( *(--mf) < lt ) *mf = lt; if ( *mf < *lm ) lm = mf; } );
	};

	auto __PropagateMLABAR = [&] (vector < t_operation > ::iterator & op)
	{
		// eAB = lt = max(eA,lt) + tB
		me = eAB.begin() - 1;
		__PropagateMFs ( op + 2 );

		// qAB = lt = max(qA,lt) + tB
		mq = qAB.end();
		__PropagateMBs ( op + 3 );

		// LABR = max(LABR,qAB+eAB)
		t_mach moe = std::min ( ( *(op+1) - 1 ) % mMach , ( *(op+3) - 1 ) % mMach ) + 2;
		if ( moe > mMach ) moe = mMach;
		moe -= 2;
		mq = qAB.begin() + moe;
		me = eAB.begin() + --moe;
		lm = mf = MLR.begin() + --moe;
		t_mach mob = std::max ( ( *(op) ) % mMach , ( *(op+2) ) % mMach );
		if ( mob ) --mob ;
		__PropagateMLxXxR ( moe - mob ); // [0, mMach-4] - [0, *] or 0 to mMach - 4
	};

	auto __PropagateMLBABR = [&] (vector < t_operation > ::iterator & op)
	{
		// eBA = lt = max(eB,lt) + tA
		me = eBA.begin() - 1;
		__PropagateMFs ( op );

		// qBA = lt = max(qB,lt) + tA
		mq = qBA.end();
		__PropagateMBs ( op + 1 );

		// LBAR = max(LBAR,qBA+eBA)
		t_mach moe = std::min ( ( *(op+1) - 1 ) % mMach , ( *(op+3) - 1 ) % mMach ) + 2;
		if ( moe > mMach ) moe = mMach;
		moe -= 2;
		mq = qBA.begin() + moe;
		me = eBA.begin() + --moe;
		lm = mf = MLR.begin() + --moe;
		t_mach mob = std::max ( ( *(op) ) % mMach , ( *(op+2) ) % mMach );
		if ( mob ) --mob ;
		__PropagateMLxXxR ( moe - mob ); // [0, mMach-4] - [0, *] or 0 to mMach - 4
	};

	static vector < vector < t_operation > ::iterator > nbs;
	nbs.reserve(ops.size());

	auto UpdateNBS = [&] ()
	{
		__PropagateMF0 ( me, lm );
		for ( vector < t_operation > ::iterator op = ops.begin(), _op = ops.end(); op < _op; ++op)
			__PropagateMF ( op, me, lm );
		assert ( Cm == *(me) );

		nbs.clear();
		__PropagateMB0 ( me, lm, mf, mq );
		t_mach fi, fl;
		{ vector < t_operation > ::iterator op = ops.end() - 1; fl = __PropagateMB ( op, me, lm, mf, mq ); }
		for ( vector < t_operation > ::iterator op = ops.end() - 3, _op = ops.begin(); op > _op; --op)
		{
			fi = __PropagateMB ( op, me, lm, mf, mq );
			if ( fl || fi )
				if ( std::max( (*(op))%mMach , (*(op+2))%mMach ) < std::min( (*(op+1)-1)%mMach , (*(op+3)-1)%mMach ) )
					nbs.push_back(op);
			fl = fi;
		}
	};

	t_time _ls_iters = 0;
	for (;;)
	{
		UpdateNBS();
		if (nbs.size() == 0) return;
		if ( _max_ls_iters < ++_ls_iters ) _max_ls_iters = _ls_iters;
		++_tot_ls_iters;
		t_time bt = Cm;
		int_fast8_t xp = 0;
		vector < t_operation > ::iterator bj = ops.end();
		for ( auto po = nbs.begin(), _po = nbs.end(); po < _po; ++po)
		{
			//positions  *po and *po+1
			st_operation delta = st_operation ( ( *po - ops.begin() ) / 2 ) * mMach;
			t_time mxBA;
			//LABR
			{
				// eA = e0 + tA
				me = eAB.begin() - 1;
				lm = Me0.begin() + delta - 1;
				__PropagateMFf ( *po );

				// qB = q0 + tB, MAB = eA + qB
				++me; assert (me == eAB.end());
				lm = Mq0.begin() + delta + 3 * mMach;
				mq = qBA.end();
				mf = MAB.end();
				__PropagateMBf ( *po + 3 );

				// eB = e0 + tB
				me = eBA.begin() - 1;
				lm = Me0.begin() + delta - 1;
				__PropagateMFf ( *po + 2 );

				// qA = q0 + tA, MBA = eB + qA
				++me; assert (me == eBA.end());
				lm = Mq0.begin() + delta + 3 * mMach;
				mq = qAB.end();
				mf = MBA.end();
				__PropagateMBf ( *po + 1 );

				// LABR = max(right(MBA),Left(MAB))
				me = MAB.begin();
				mq = MBA.end() - 1;
				mxBA = __PropagateMLR(); // lm is the minimum in MLR
			}
			if (mxBA < bt)
			{
				// Mark all job to swap as best choice
				bt = mxBA;
				xp = 0;
				bj = *po;
			}
			if ( xp /* != 0 */ ) if ( mxBA == bt )
			{
				// Mark all job to swap as best choice, prefer swap all job over split ops
				bt = mxBA;
				xp = 0;
				bj = *po;
			}
			if ( *lm < bt )
			{
				__PropagateMLABAR(*po);
				if ( *lm < bt )
				{
					bt = *lm;
					xp = lm - MLR.end();
					bj = *po;
				}
				continue;
			}
			{
				// LBAR = max(right(MAB),Left(MBA))
				me = MBA.begin();
				mq = MAB.end() - 1;
				__PropagateMLR(); // lm is the minimum in MLR
			}
			if ( *lm < bt )
			{
				__PropagateMLBABR(*po);
				if ( *lm < bt )
				{
					bt = *lm;
					xp = lm - MLR.begin() + 2;
					bj = *po;
				}
			}
		}

		#ifndef NDEBUG
		auto lop = ops;
		#endif
		if ( bt >= Cm ) return;
		if ( xp == 0 )
		{
			vector < t_operation > ::iterator be = bj + 2;
			if ( bj > ops.begin() && *(bj-2)/mMach == *be/mMach ) { *(bj-1) = *(++be); ++be; }
			else { t_operation t = *bj; *bj = *be; *be = t; t = *(++bj); *bj = *(++be); *be = t; ++be; ++bj; }
			if ( be < ops.end() && (*bj)/mMach == (*be)/mMach ) ++be;
			else ++bj;
			ops.erase(++bj,be);
		}
		else if ( xp > 0 )
		{
			// insert BAB
			vector < t_operation > ::iterator be = bj + 2;
			t_operation ob = *(be);
			t_operation oe = ob - ( ob ) % mMach + t_operation(xp);
			*be = oe + 1;
			if ( bj > ops.begin() && *(bj-2)/mMach == ob/mMach ) *(bj-1) = oe;
			else ops.insert ( bj, { ob, oe } );
		}
		else
		{
			// insert ABA
			vector < t_operation > ::iterator be = bj;
			t_operation ob = *(be);
			ob += mMach - ob % mMach - t_operation(-xp); // xp is negative
			t_operation oe = *(++be);
			*be = ob - 1;
			be+=3;
			if ( be < ops.end() && ob/mMach == (*be)/mMach ) *be = ob;
			else ops.insert ( be, { ob, oe } );
		}
		if (_max_swap_size < ops.size()) _max_swap_size = ops.size();
		Cm = bt;
		#ifndef NDEBUG
		VerifyCm();
		#endif
	}
}

////////////////////////////////////////////////////////////
// Constructive Heuristics

inline
void t_solution::_NEH_priority(  vector < t_operation > & prt )
{
	vector < t_time > T;
	prt.resize(t_size_type(nJobs));
	T.resize(t_size_type(nJobs));
	vector < t_time > ::iterator po = p.begin() + 1;
	// Calculate total time for each job.
	for ( auto & t : T )
	{
		t = 0;
		for (vector < t_time > ::iterator _po = po + mMach; po < _po; ++po) t += (*po);
	}
	iota(prt.begin(),prt.end(),0);
	std::stable_sort( prt.begin(), prt.end(),
		[&T](const t_operation & i, const t_operation & j) { return (T[t_size_type(i)]>T[t_size_type(j)] ||(T[t_size_type(i)]==T[t_size_type(j)] && i<j)); } );
	jobs.resize(t_size_type(nJobs));
	auto t = jobs.begin();
	for(auto & a : prt) { *(t++) = a; a = a * mMach + 1; }
}

bool is91=false;
inline
void t_solution::_AD_priority(  vector < t_operation > & prt )
{
	vector < double > T;
	prt.resize(t_size_type(nJobs));
	T.resize(t_size_type(nJobs));
	vector < t_time > ::iterator po = p.begin() + 1;
	// Calculate Average and Standard Deviation for each job.
	for ( auto & t : T )
	{
		t_time S1 = 0;
		t_time S2 = 0;
		for (vector < t_time > ::iterator _po = po + mMach; po < _po; ++po)
		{
			S1 += (*po);
			S2 += (*po) * (*po);
		}
		t = double ( S1 ) / double ( mMach ); // AVG_j
		t += sqrt ( double ( t_time(mMach) * S2 - S1 * S1 ) / double ( mMach * ( mMach - 1 ) ) ); // SDV_j
	}
	iota(prt.begin(),prt.end(),0);
	if (is91)
	std::stable_sort( prt.begin(), prt.end(),
		[&T](const t_operation & i, const t_operation & j) { return (T[t_size_type(i)]>T[t_size_type(j)] ||(T[t_size_type(i)]==T[t_size_type(j)] && i>j)); } );
	else
	std::stable_sort( prt.begin(), prt.end(),
		[&T](const t_operation & i, const t_operation & j) { return (T[t_size_type(i)]>T[t_size_type(j)] ||(T[t_size_type(i)]==T[t_size_type(j)] && i<j)); } );
	jobs.resize(t_size_type(nJobs));
	auto t = jobs.begin();
	for(auto & a : prt) { *(t++) = a; a = a * mMach + 1; }
}

inline
void t_solution::_ADS_priority(  vector < t_operation > & prt )
{
	vector < double > T;
	prt.resize(t_size_type(nJobs));
	T.resize(t_size_type(nJobs));
	vector < t_time > ::iterator po = p.begin() + 1;
	// Calculate AVG, STDEV and SKW for each job.
	for ( auto & t : T )
	{
		uint_fast64_t S1 = 0;
		uint_fast64_t S2 = 0;
		uint_fast64_t S3 = 0;
		for (vector < t_time > ::iterator _po = po + mMach; po < _po; ++po)
		{
			t_time _T2 = (*po);
			S1 += _T2; _T2 *= (*po);
			S2 += _T2; _T2 *= (*po);
			S3 += _T2;
		}
		t = double(S1) / double(mMach); // AVG_j
		double tt = sqrt ( double ( uint_fast8_t (mMach) * S2 - S1 * S1 ) );
		t += tt / sqrt ( double ( mMach * ( mMach - 1 ) ) ); // SDV_j
		t += std::abs( ( double ( S3 * uint_fast8_t (mMach) * uint_fast8_t (mMach) + 2 * S1 * S1 * S1) - double ( S1 * S2 * 3 * uint_fast8_t ( mMach )) ) / double ( tt * tt * tt ) ); // SKE_j
	}
	iota(prt.begin(),prt.end(),0);
	std::stable_sort( prt.begin(), prt.end(),
		[&T](const t_operation & i, const t_operation & j) { return (T[t_size_type(i)]>T[t_size_type(j)] ||(T[t_size_type(i)]==T[t_size_type(j)] && i<j)); } );
	auto t = jobs.begin();
	for(auto & a : prt) { *(t++) = a; a = a * mMach + 1; }
}

template < t_solution::_t_priority _priority, t_solution::_t_InsertJob _InsertJob, t_solution::_t_InsertJob _InsertJobNP >
inline
void t_solution::Create_NEH_NP(int_fast16_t sp )
{
	vector < t_operation > prt;
	ops.reserve(t_size_type(3*nJobs));
	(this->*_priority) (prt);
	t_operation o = prt.front();
	ops.resize(2);
	ops[0] = o;
	ops[1] = o + mMach - 1;
	vector < t_operation > ::iterator pr = prt.begin() + 1, _pr = prt.end() - sp*int_fast16_t(nJobs)/10;
	for (; pr < _pr; ++pr ) (this->*_InsertJob) ( *pr );
	_pr = prt.end();
	for (; pr < _pr; ++pr ) (this->*_InsertJobNP) ( *pr );
	#ifndef NDEBUG
	VerifyCm();
	#endif
}

inline
void t_solution::Create_F5_NP(int_fast16_t sp = 2)
{
	vector < t_operation > prt;
	ops.reserve(t_size_type(3*nJobs));
	_NEH_priority(prt);
	t_operation o = prt.front();
	ops.resize(2);
	ops[0] = o;
	ops[1] = o + mMach - 1;
	jobs.resize(1);
	jobs.front()=o/mMach;

	vector < t_operation > ::iterator pr = prt.begin() + 1, _pr = prt.end() - sp*int_fast16_t(nJobs)/10;
	for (; pr < _pr; ++pr )
	{
		InsertJobOp < false >  ( *pr );
		jobs.push_back ( *pr/mMach );
		LocalSearch_Insertion < &_solution::InsertJobOp < false > > ();
	}
	_pr = prt.end();
	for (; pr < _pr; ++pr )
	{
		InsertJobOp_NP < false >  ( *pr );
		jobs.push_back ( *pr/mMach );
		LocalSearch_Insertion < &_solution::InsertJobOp_NP < false > > ();
	}
	#ifndef NDEBUG
	VerifyCm();
	#endif
}

inline
void t_solution::Create_RN_NP(int_fast16_t sp = 4)
{
	vector < t_operation > prt;
	ops.reserve(t_size_type(3*nJobs));
	_NEH_priority(prt);
	t_operation o = prt.front();
	ops.resize(2);
	ops[0] = o;
	ops[1] = o + mMach - 1;

	t_job t = nJobs - t_job(sp)*(nJobs)/10;
	vector < t_operation > ::iterator pr = prt.begin() + 1;
	for (vector < t_operation > ::iterator _pr = prt.begin() + int_fast16_t(t>4?4:t); pr < _pr; ++pr )
	{
		InsertJobOp < false >  ( *pr );
	}
	for (vector < t_operation > ::iterator _pr = prt.begin() + int_fast16_t(t); pr < _pr; ++pr )
	{
		InsertJobOp < false >  ( *pr );
		PairSearch_Insertion < &_solution::InsertJobOp < false > > ();
	}
	for (vector < t_operation > ::iterator _pr = prt.begin() + 4; pr < _pr; ++pr )
	{
		InsertJobOp_NP < false >  ( *pr );
	}
	for (vector < t_operation > ::iterator _pr = prt.end(); pr < _pr; ++pr )
	{
		InsertJobOp_NP < false >  ( *pr );
		PairSearch_Insertion < &_solution::InsertJobOp_NP < false > > ();
	}
	#ifndef NDEBUG
	VerifyCm();
	#endif
}

inline
void t_solution::Create_Pa_NP(int_fast16_t sp = 6)
{
	vector < t_operation > prt;
	ops.reserve(t_size_type(3*nJobs));
	_NEH_priority(prt);
	t_operation o = prt.front();
	ops.resize(2);
	ops[0] = o;
	ops[1] = o + mMach - 1;

	t_job t = nJobs - t_job(sp)*(nJobs)/10;
	vector < t_operation > ::iterator pr = prt.begin() + 1;
	for (vector < t_operation > ::iterator _pr = prt.begin() + int_fast16_t(t>4?4:t); pr < _pr; ++pr )
	{
		InsertJobOp < false >  ( *pr );
	}
	for (vector < t_operation > ::iterator _pr = prt.begin() + int_fast16_t(t); pr < _pr; ++pr )
	{
		InsertJobOp < false >  ( *pr );
		LocalSearch_PRInsertionAll < &_solution::InsertJobOp < false >, false > ();
	}
	for (vector < t_operation > ::iterator _pr = prt.begin() + 4; pr < _pr; ++pr )
	{
		InsertJobOp_NP < false >  ( *pr );
	}
	for (vector < t_operation > ::iterator _pr = prt.end(); pr < _pr; ++pr )
	{
		InsertJobOp_NP < false >  ( *pr );
		LocalSearch_PRInsertionAll < &_solution::InsertJobOp_NP < false >, false > ();
	}
	#ifndef NDEBUG
	VerifyCm();
	#endif
}

inline
void t_solution::Create_Pc_NP(int_fast16_t sp = 3)
{
	vector < t_operation > prt;
	ops.reserve(t_size_type(3*nJobs));
	_NEH_priority(prt);
	t_operation o = prt.front();
	ops.resize(2);
	ops[0] = o;
	ops[1] = o + mMach - 1;

	t_job t = nJobs - t_job(sp)*(nJobs)/10;
	vector < t_operation > ::iterator pr = prt.begin() + 1;
	for (vector < t_operation > ::iterator _pr = prt.begin() + int_fast16_t(t>4?4:t); pr < _pr; ++pr )
	{
		InsertJobOp < false >  ( *pr );
	}
	for (vector < t_operation > ::iterator _pr = prt.begin() + int_fast16_t(t); pr < _pr; ++pr )
	{
		InsertJobOp < false >  ( *pr );
		LocalSearch_PRInsertionCrt < &_solution::InsertJobOp < false >, false > ();
	}
	for (vector < t_operation > ::iterator _pr = prt.begin() + 4; pr < _pr; ++pr )
	{
		InsertJobOp_NP < false >  ( *pr );
	}
	for (vector < t_operation > ::iterator _pr = prt.end(); pr < _pr; ++pr )
	{
		InsertJobOp_NP < false >  ( *pr );
		LocalSearch_PRInsertionCrt < &_solution::InsertJobOp_NP < false >, false > ();
	}
	#ifndef NDEBUG
	VerifyCm();
	#endif
}

template < t_solution::_t_priority _priority >
inline
void t_solution::Create_BRN_NP(int_fast16_t sp )
{
	vector < t_operation > prt;
	ops.reserve(t_size_type(3*nJobs));
	(this->*_priority) (prt);
	t_operation o = prt.front();
	ops.resize(2);
	ops[0] = o;
	ops[1] = o + mMach - 1;

	t_job t = nJobs - t_job(sp)*(nJobs)/10;
	vector < t_operation > ::iterator pr = prt.begin() + 1;
	for (vector < t_operation > ::iterator _pr = prt.begin() + int_fast16_t(t); pr < _pr; ++pr )
	{
		InsertJobOp < false >  ( *pr );
	}
	for (vector < t_operation > ::iterator _pr = prt.end(); pr < _pr; ++pr )
	{
		InsertJobOp_NP < false >  ( *pr );
		LocalSearch_fastN5_Cm_NP ();
	}
	#ifndef NDEBUG
	VerifyCm();
	#endif
}

//////////////////////////////////////////////////////////////////////
//   ITERATED GREEDY ALGORITHMS for NPFSSP

template < t_solution::_t_Construct _construct, t_solution::_t_InsertJob _InsertJob, t_solution::_t_LocalSearch _localsearch >
inline
void IGLS_Cm( t_solution & bs, int_fast16_t sp = 0 )
{
	double tmpt = double (psum) / ( mnOps * 25 ); //i.e. alpha * ( TotTime / mnOps) / 10; alpha = 0.4;
	t_solution ms, ns;

	_max_ls_iters = 0;
	_tot_ls_iters = 0;
	_max_swap_size = 2*t_size_type(nJobs);
	t_elapsed _bt = 0;

	elapsed(/* reset = */ true);

	(ms.*_construct)(sp);
	#ifndef NDEBUG
	ms.VerifyCm();
	#endif

	t_time Cm0 = ms.Cm;
	(ms.*_localsearch)();
	(bs).Cm = ms.Cm;
	(bs).ops = ms.ops;
	t_elapsed iters = 0;
	t_elapsed lt = elapsed();

	fout << " S0 " << Cm0 << " " << lt << " " << ms.Cm << " " << _max_ls_iters;
	fout << " " << (_max_swap_size/2-t_size_type(nJobs)) << " " << ((_max_swap_size*500) / t_size_type(nJobs) - 1000);
	_max_ls_iters = 0;
	_tot_ls_iters = 0;
	_max_swap_size = 2*t_size_type(nJobs);

	while ( lt < _timelimit )
	{
		// Perturbate
		std::random_shuffle( jobs.begin(), jobs.end() );
		ns.Cm = ms.Cm;
		ns.ops = ms.ops;
		{
			vector < t_job > ::iterator jsb = jobs.end() - destroyNCm;
			ns.DeleteJobs ( jsb, jobs.end() );
			for (vector < t_job > ::iterator _j = jobs.end(); jsb < _j; ++jsb )
				(ns.*_InsertJob) ( *jsb * mMach + 1 );
		}
		(ns.*_localsearch)();

		// check statistics
		lt = elapsed();
		++iters;

		// update best
		if ( ( ns.Cm < ms.Cm ) ||
				( double(rand()) / RAND_MAX < exp ( - ( double(ns.Cm-ms.Cm) / tmpt ) ) ) )
		{
			ms.Cm = ns.Cm;
			ms.ops.swap(ns.ops);
			if ( ms.Cm < (bs).Cm )
			{
				_bt = lt;
				(bs).Cm = ms.Cm;
				(bs).ops = ms.ops;
			}
		}

		// timecheck
		if ( lt >= _timecheck )
		{
			_timecheck += t_elapsed(TCHK*mnOps);
			fout << " " << lt << " " << iters << " " << (bs).Cm << " " << _bt << " " << double(_tot_ls_iters)/double(iters) << " " << _max_ls_iters;
			fout << " " << (_max_swap_size/2-t_size_type(nJobs)) << " " << ((_max_swap_size*500) / t_size_type(nJobs) - 1000);
		}
	}

	fout << std::endl << " Sol ";
	(bs).Evaluate();
	(bs).print();
	lt = elapsed();
}


////////////////////////////////////////////////////////////
//  main program

int main(int argc, char** argv)
{
	uint_fast8_t rtst = 0;
	uint_fast8_t rptt = 34;
	uint_fast8_t inst = 180;

	uint_fast8_t nonpermut = 0;
	uint_fast8_t construct = 0;
	uint_fast8_t lclsearch = 0;
	t_solution xs;

	if ( argc < 2 )
	{
		std::cout
			<< "\nFast heuristics for minimizing the makespan in non-permutation flow shops.\nBenavides, A.J. and Ritt, M., 2018.\nComputers & Operations Research, 100, pp.230-243.\n\n"
			<< "Usage:\n\tpnpFSSP <inst> <pnp> <cnstr> <lsrch>\n\nParameters:\n"
			<< " inst : Number of the instance in the benchmark.\n\tIf not given, displays this help.\n\n"
			<< " pnp  : Selects a permutation/non-permutation Iterated Greedy Algorithm (IG): \n\t0 for a permutation IG, and 1 for a non-permutation IG.\n\tIf not given, tests all constructive heuristic combinations (Table 6).\n\n"
			<< " cnstr: Selects the constructive heuristic for the IG using the numeric value\n\tin parenthesis: BR_0 (0), BR_F5 (1), BR_R (2), BR_Pa (3), BR_Pc (4),\n\tBR_RN (5), or BR_FF (6). If not given, the default is BR_0 (0).\n\n"
			<< " lsrch: Selects the local search heuristic for the IG using the numeric value\n\tin parenthesis: Ins (0), Pa (1), Pc (2), or RNB (3).\n\tIf not given, the default is Ins (0).\n\n"
			<< "To use another benchmark, you must change the only hard-coded parameter\nby uncommenting one of the next three lines in the source code:\n// #define TAILLARD\n// #define VRF_S\n// #define VRF_L\n\n";
		return 0;
	}

	int_fast16_t csp = 0;
	inst = (argc > 1)? std::stoi(std::string(argv[1])): 180;
	nonpermut = (argc > 2)? std::stoi(std::string(argv[2])): 0;
	construct = (argc > 3)? std::stoi(std::string(argv[3])): 0;
	lclsearch = (argc > 4)? std::stoi(std::string(argv[4])): 0;

	#if defined TAILLARD
	{
		is91 = (inst == 91); // adjust tiebreaker Fernandez-Viagas & Framiñan
	}
	#endif

	srand(time(0)+inst*100);
	unsigned int seed = unsigned(std::rand());

	{
		std::string file;
		std::string fl;
		file.reserve(60);
		fl.reserve(20);

		#if defined TAILLARD
			fl = "ta000"; // TA instances
		#elif defined VRF_S
			fl = "vrfs000"; // VRF_S instances
		#elif defined VRF_L
			fl = "vrfl000"; // VRF_L instances
		#endif
		*((fl).end()-3) = '0' + ( inst / 100 );
		*((fl).end()-2) = '0' + ((inst / 10) % 10);
		*((fl).end()-1) = '0' + ( inst % 10 );
		(file) = "../flowshop/" + fl;

		load_operations(file);
		file.assign(fl);
		file.append(".p00");

		#ifndef NDEBUG
		for (auto & x : Me1) x = unsigned(rand()%133);
		for (auto & x : Mq0) x = unsigned(rand()%133);
		for (auto & x : Me0) x = unsigned(rand()%133);
		for ( auto me  = Me0.begin() - 1, lm = me+mMach; me <= lm;) *(++me) = 0;
		#endif

		if ( argc < 3 )
		{
			timeMeasure = 1000000.0; // redefinition to microsecond
			vector <t_elapsed> tmps;
			tmps.reserve(80);
			vector <t_time> mlsi;
			mlsi.reserve(10);
			vector <t_time> mswp;
			mswp.reserve(10);
			uint_fast8_t _it = 0;
			const int trps = (nJobs < 100)? 10: 1;

			*(file.end()-2) = '9';
			*(file.end()-1) = '9';
			fout.open( file );

			auto __TestConstruction = [&] (uint_fast8_t maxsp, std::string sCnstr, t_solution::_t_Construct _construct)
			{
				_max_ls_iters = 0;
				_max_swap_size = 2*t_size_type(nJobs);
				for ( uint_fast8_t sp = 0; sp <= maxsp; ++sp )
				{
					elapsed(true);
					for ( uint_fast8_t c = trps; c; --c )
						(xs.*_construct) (sp);
					fout << "Rslt " << fl << " " << nJobs << " " << int(mMach);
					fout << sCnstr << int (sp);
					fout << " " << xs.Cm;
					fout << " " << elapsed()/t_elapsed(trps);
					fout << std::endl;
				}
				mlsi.push_back ( _max_ls_iters );
				mswp.push_back ( _max_swap_size );
			};

			__TestConstruction ( 10, " NEH ", &_solution::Create_NEH_NP < &_solution::_NEH_priority, &_solution::InsertJobOp < false > , &_solution::InsertJobOp_NP < false > > );
			__TestConstruction ( 10, " BRN ", &_solution::Create_BRN_NP < &_solution::_NEH_priority > );
			__TestConstruction ( 10, " FF ", &_solution::Create_NEH_NP < &_solution::_AD_priority, &_solution::InsertJobOpFF, &_solution::InsertJobOpFF_NP > );
			__TestConstruction ( 10, " F5 ", &_solution::Create_F5_NP );
			__TestConstruction ( 10, " RN ", &_solution::Create_RN_NP );
			__TestConstruction ( 10, " Pa ", &_solution::Create_Pa_NP );
			__TestConstruction ( 10, " Pc ", &_solution::Create_Pc_NP );
			__TestConstruction (  0, " LJP ", &_solution::Create_NEH_NP < &_solution::_ADS_priority, &_solution::InsertJobOpLJP, &_solution::InsertJobOpLJP > );

			fout << " Stats " << fl << " " << nJobs << " " << int(mMach);
			fout << " * "; for ( auto & i : mlsi )  fout << " " << i;
			fout << " * "; for ( auto & i : mswp )  fout << " " << i;
			fout << std::endl;
			fout.close();
			return 0;
		}

		srand(seed);
		for ( unsigned short int i = rtst; i <= rtst + rptt /* 35 times */; ++i )
		{
			// open respective output file
			*(file.end()-2) = '0' + ( i / 10 );
			*(file.end()-1) = '0' + ( i % 10 );
			fout.open( file );

			_timecheck = t_elapsed(TCHK*mnOps);
			_timelimit = t_elapsed(TLMT*mnOps);

			seed = unsigned(std::rand());
			//seed = (argc > 5)? std::stoi(std::string(argv[4])): 0;
			srand(seed);
			fout << "Rslt " << fl << " " << nJobs << " " << int(mMach) << " " << seed;

			if ( nonpermut )
			{
				fout << " NS C" << int(construct) << " L" << int(lclsearch);
				switch ( construct )
				{
					case 0: default: csp = 5; switch ( lclsearch )
					{
						case 0: default:
						IGLS_Cm <
							&_solution::Create_NEH_NP < &_solution::_NEH_priority, &_solution::InsertJobOp < false > , &_solution::InsertJobOp_NP < false > >,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_Insertion < &_solution::InsertJobOp_NP > > ( xs, csp );
						break;
						case 1:
						IGLS_Cm <
							&_solution::Create_NEH_NP < &_solution::_NEH_priority, &_solution::InsertJobOp < false > , &_solution::InsertJobOp_NP < false > >,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_PRInsertionAll < &_solution::InsertJobOp_NP > > ( xs, csp );
						break;
						case 2:
						IGLS_Cm <
							&_solution::Create_NEH_NP < &_solution::_NEH_priority, &_solution::InsertJobOp < false > , &_solution::InsertJobOp_NP < false > >,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_PRInsertionCrt < &_solution::InsertJobOp_NP > > ( xs, csp );
						break;
						case 3:
						IGLS_Cm <
							&_solution::Create_NEH_NP < &_solution::_NEH_priority, &_solution::InsertJobOp < false > , &_solution::InsertJobOp_NP < false > >,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_fastN5_Cm_NP > ( xs, csp );
					}
					break;
					case 1: csp = 1; switch ( lclsearch )
					{
						case 0: default:
						IGLS_Cm <
							&_solution::Create_F5_NP,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_Insertion < &_solution::InsertJobOp_NP > > ( xs, csp );
						break;
						case 1:
						IGLS_Cm <
							&_solution::Create_F5_NP,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_PRInsertionAll < &_solution::InsertJobOp_NP > > ( xs, csp );
						break;
						case 2:
						IGLS_Cm <
							&_solution::Create_F5_NP,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_PRInsertionCrt < &_solution::InsertJobOp_NP > > ( xs, csp );
						break;
						case 3:
						IGLS_Cm <
							&_solution::Create_F5_NP,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_fastN5_Cm_NP > ( xs, csp );
					}
					break;
					case 2: csp = 1; switch ( lclsearch )
					{
						case 0: default:
						IGLS_Cm <
							&_solution::Create_RN_NP,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_Insertion < &_solution::InsertJobOp_NP > > ( xs, csp );
						break;
						case 1:
						IGLS_Cm <
							&_solution::Create_RN_NP,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_PRInsertionAll < &_solution::InsertJobOp_NP > > ( xs, csp );
						break;
						case 2:
						IGLS_Cm <
							&_solution::Create_RN_NP,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_PRInsertionCrt < &_solution::InsertJobOp_NP > > ( xs, csp );
						break;
						case 3:
						IGLS_Cm <
							&_solution::Create_RN_NP,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_fastN5_Cm_NP > ( xs, csp );
					}
					break;
					case 3: csp = 1; switch ( lclsearch )
					{
						case 0: default:
						IGLS_Cm <
							&_solution::Create_Pa_NP,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_Insertion < &_solution::InsertJobOp_NP > > ( xs, csp );
						break;
						case 1:
						IGLS_Cm <
							&_solution::Create_Pa_NP,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_PRInsertionAll < &_solution::InsertJobOp_NP > > ( xs, csp );
						break;
						case 2:
						IGLS_Cm <
							&_solution::Create_Pa_NP,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_PRInsertionCrt < &_solution::InsertJobOp_NP > > ( xs, csp );
						break;
						case 3:
						IGLS_Cm <
							&_solution::Create_Pa_NP,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_fastN5_Cm_NP > ( xs, csp );
					}
					break;
					case 4: csp = 2; switch ( lclsearch )
					{
						case 0: default:
						IGLS_Cm <
							&_solution::Create_Pc_NP,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_Insertion < &_solution::InsertJobOp_NP > > ( xs, csp );
						break;
						case 1:
						IGLS_Cm <
							&_solution::Create_Pc_NP,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_PRInsertionAll < &_solution::InsertJobOp_NP > > ( xs, csp );
						break;
						case 2:
						IGLS_Cm <
							&_solution::Create_Pc_NP,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_PRInsertionCrt < &_solution::InsertJobOp_NP > > ( xs, csp );
						break;
						case 3:
						IGLS_Cm <
							&_solution::Create_Pc_NP,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_fastN5_Cm_NP > ( xs, csp );
					}
					break;
					case 5: csp = 3; switch ( lclsearch )
					{
						case 0: default:
						IGLS_Cm <
							&_solution::Create_BRN_NP < &_solution::_NEH_priority >,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_Insertion < &_solution::InsertJobOp_NP > > ( xs, csp );
						break;
						case 1:
						IGLS_Cm <
							&_solution::Create_BRN_NP < &_solution::_NEH_priority >,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_PRInsertionAll < &_solution::InsertJobOp_NP > > ( xs, csp );
						break;
						case 2:
						IGLS_Cm <
							&_solution::Create_BRN_NP < &_solution::_NEH_priority >,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_PRInsertionCrt < &_solution::InsertJobOp_NP > > ( xs, csp );
						break;
						case 3:
						IGLS_Cm <
							&_solution::Create_BRN_NP < &_solution::_NEH_priority >,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_fastN5_Cm_NP > ( xs, csp );
					}
					break;
					case 6: csp = 4; switch ( lclsearch )
					{
						case 0: default:
						IGLS_Cm <
							&_solution::Create_NEH_NP < &_solution::_AD_priority, &_solution::InsertJobOpFF, &_solution::InsertJobOpFF_NP >,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_Insertion < &_solution::InsertJobOp_NP > > ( xs, csp );
						break;
						case 1:
						IGLS_Cm <
							&_solution::Create_NEH_NP < &_solution::_AD_priority, &_solution::InsertJobOpFF, &_solution::InsertJobOpFF_NP >,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_PRInsertionAll < &_solution::InsertJobOp_NP > > ( xs, csp );
						break;
						case 2:
						IGLS_Cm <
							&_solution::Create_NEH_NP < &_solution::_AD_priority, &_solution::InsertJobOpFF, &_solution::InsertJobOpFF_NP >,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_PRInsertionCrt < &_solution::InsertJobOp_NP > > ( xs, csp );
						break;
						case 3:
						IGLS_Cm <
							&_solution::Create_NEH_NP < &_solution::_AD_priority, &_solution::InsertJobOpFF, &_solution::InsertJobOpFF_NP >,
							&_solution::InsertJobOp_NP,
							&_solution::LocalSearch_fastN5_Cm_NP > ( xs, csp );
					}
				}
			}
			else
			{
				fout << " PS C" << int(construct) << " L" << int(lclsearch);
				switch ( construct )
				{
					case 0: default: switch ( lclsearch )
					{
						case 0: default:
						IGLS_Cm <
							&_solution::Create_NEH_NP < &_solution::_NEH_priority, &_solution::InsertJobOp < false > , &_solution::InsertJobOp_NP < false > >,
							&_solution::InsertJobOp,
							&_solution::LocalSearch_Insertion < &_solution::InsertJobOp > > ( xs, 0 );
						break;
						case 1:
						IGLS_Cm <
							&_solution::Create_NEH_NP < &_solution::_NEH_priority, &_solution::InsertJobOp < false > , &_solution::InsertJobOp_NP < false > >,
							&_solution::InsertJobOp,
							&_solution::LocalSearch_PRInsertionAll < &_solution::InsertJobOp > > ( xs, 0 );
						break;
						case 2:
						IGLS_Cm <
							&_solution::Create_NEH_NP < &_solution::_NEH_priority, &_solution::InsertJobOp < false > , &_solution::InsertJobOp_NP < false > >,
							&_solution::InsertJobOp,
							&_solution::LocalSearch_PRInsertionCrt < &_solution::InsertJobOp > > ( xs, 0 );
					}
					break;
					case 1: switch ( lclsearch )
					{
						case 0: default:
						IGLS_Cm <
							&_solution::Create_F5_NP,
							&_solution::InsertJobOp,
							&_solution::LocalSearch_Insertion < &_solution::InsertJobOp > > ( xs, 0 );
						break;
						case 1:
						IGLS_Cm <
							&_solution::Create_F5_NP,
							&_solution::InsertJobOp,
							&_solution::LocalSearch_PRInsertionAll < &_solution::InsertJobOp > > ( xs, 0 );
						break;
						case 2:
						IGLS_Cm <
							&_solution::Create_F5_NP,
							&_solution::InsertJobOp,
							&_solution::LocalSearch_PRInsertionCrt < &_solution::InsertJobOp > > ( xs, 0 );
					}
					break;
					case 2: switch ( lclsearch )
					{
						case 0: default:
						IGLS_Cm <
							&_solution::Create_RN_NP,
							&_solution::InsertJobOp,
							&_solution::LocalSearch_Insertion < &_solution::InsertJobOp > > ( xs, 0 );
						break;
						case 1:
						IGLS_Cm <
							&_solution::Create_RN_NP,
							&_solution::InsertJobOp,
							&_solution::LocalSearch_PRInsertionAll < &_solution::InsertJobOp > > ( xs, 0 );
						break;
						case 2:
						IGLS_Cm <
							&_solution::Create_RN_NP,
							&_solution::InsertJobOp,
							&_solution::LocalSearch_PRInsertionCrt < &_solution::InsertJobOp > > ( xs, 0 );
					}
					break;
					case 3: switch ( lclsearch )
					{
						case 0: default:
						IGLS_Cm <
							&_solution::Create_Pa_NP,
							&_solution::InsertJobOp,
							&_solution::LocalSearch_Insertion < &_solution::InsertJobOp > > ( xs, 0 );
						break;
						case 1:
						IGLS_Cm <
							&_solution::Create_Pa_NP,
							&_solution::InsertJobOp,
							&_solution::LocalSearch_PRInsertionAll < &_solution::InsertJobOp > > ( xs, 0 );
						break;
						case 2:
						IGLS_Cm <
							&_solution::Create_Pa_NP,
							&_solution::InsertJobOp,
							&_solution::LocalSearch_PRInsertionCrt < &_solution::InsertJobOp > > ( xs, 0 );
					}
					break;
					case 4: switch ( lclsearch )
					{
						case 0: default:
						IGLS_Cm <
							&_solution::Create_Pc_NP,
							&_solution::InsertJobOp,
							&_solution::LocalSearch_Insertion < &_solution::InsertJobOp > > ( xs, 0 );
						break;
						case 1:
						IGLS_Cm <
							&_solution::Create_Pc_NP,
							&_solution::InsertJobOp,
							&_solution::LocalSearch_PRInsertionAll < &_solution::InsertJobOp > > ( xs, 0 );
						break;
						case 2:
						IGLS_Cm <
							&_solution::Create_Pc_NP,
							&_solution::InsertJobOp,
							&_solution::LocalSearch_PRInsertionCrt < &_solution::InsertJobOp > > ( xs, 0 );
					}
					break;
					case 5: switch ( lclsearch )
					{
						case 0: default:
						IGLS_Cm <
							&_solution::Create_NEH_NP < &_solution::_AD_priority, &_solution::InsertJobOpFF, &_solution::InsertJobOpFF >,
							&_solution::InsertJobOpFF,
							&_solution::LocalSearch_Insertion < &_solution::InsertJobOpFF > > ( xs, 0 );
						break;
						case 1:
						IGLS_Cm <
							&_solution::Create_NEH_NP < &_solution::_AD_priority, &_solution::InsertJobOpFF, &_solution::InsertJobOpFF >,
							&_solution::InsertJobOpFF,
							&_solution::LocalSearch_PRInsertionAll < &_solution::InsertJobOpFF > > ( xs, 0 );
						break;
						case 2:
						IGLS_Cm <
							&_solution::Create_NEH_NP < &_solution::_AD_priority, &_solution::InsertJobOpFF , &_solution::InsertJobOpFF >,
							&_solution::InsertJobOpFF,
							&_solution::LocalSearch_PRInsertionCrt < &_solution::InsertJobOpFF > > ( xs, 0 );
					}
				}
			}
			fout << std::endl;
			fout.close();
		}
	}
	return 0;
}
