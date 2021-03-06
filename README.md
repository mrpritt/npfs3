# Fast heuristics for minimizing the makespan in non-permutation flow shops

This repository contains detailed results and code for the paper [Fast heuristics for minimizing the makespan in non-permutation flow shops](https://doi.org/10.1016/j.cor.2018.07.017).

## Detailed results

1.  [Best known values used in relative deviations](data/instances.csv).
2.  [Performance of variants of the constructive BR heuristic in Table 6](data/vsall.csv).
3.  [Performance of constructive heuristics on the instances of Taillard in Table 7](data/taall.csv).
4.  Performance of constructive heuristics on all instances in Table 8: [VRF-small](data/vsall.csv), [VRF-large](data/vlall.csv).
5.  [Performance of permutation IG heuristics on the instances of Taillard in Table 9](data/igPta.csv).
6.  [Performance of the non-permutation IG heuristics on the instances of Taillard in Table 10](data/igNta.csv).
7.  Comparison of state-of-the-art methods for the permutation and non-permutation FSSP on the instances of Taillard in Table 12: contained in data files of items 5 and 6.
8.  Comparison of state-of-the-art methods for the permutation and non-permutation FSSP on all instances in Table 13: additionally to above tables for the non-permutation flow shop [VRF-small](data/igPvs.csv), [VRF-large](data/igPvl.csv), and for the non-permutation flow shop [VRF-small](data/igNvs.csv), [VRF-large](data/igNvl.csv).
9.  Number of iterations in Table 14: see time and number of iterations in the above data files.

## Code

The code is contained in the single file [pnpFSSP.cpp](src/pnpFSSP.cpp). To compile use
```bash
g++ -O2 --static --fast-math -std=c++17 -DNDEBUG pnpFSSP.cpp -o pnpFSSP
```

## How to cite
```bibtex
@Article{Benavides.Ritt/2018,
  author = 	 {Alexander Benavides and Marcus Ritt},
  title = 	 {Fast heuristics for minimizing the makespan in non-permutation flow shops},
  journal =	 "Comp. Oper. Res.",
  year = 	 {2018},
  volume =	 {100},
  pages =	 {230--243},
  month =	 dec,
  doi = 	 {10.1016/j.cor.2018.07.017}
}
```
