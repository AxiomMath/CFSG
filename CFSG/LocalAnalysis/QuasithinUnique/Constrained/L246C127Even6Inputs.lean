module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenCertDefs

public section

namespace CFSG.QuasithinUnique.L246C127.Even6
open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

@[expose] def mGens : List (Perm (Fin 6)) :=
  [permOf 6 [[0,1,2]], permOf 6 [[1,2,3,4,5]]]

@[expose] def tGens : List (Perm (Fin 6)) :=
  [permOf 6 [[0,1],[4,5]], permOf 6 [[0,2],[1,3]]]

@[expose] def L1 : List (Perm (Fin 6)) :=
  [permOf 6 [[0,1],[4,5]], permOf 6 [[0,2],[1,3]], permOf 6 [[2,4],[3,5]]]

@[expose] def L2 : List (Perm (Fin 6)) :=
  [permOf 6 [[0,1],[4,5]], permOf 6 [[0,2],[1,3]], permOf 6 [[1,2],[4,5]]]

@[expose] def L3 : List (Perm (Fin 6)) :=
  [permOf 6 [[0,1],[4,5]], permOf 6 [[0,2],[1,3]], permOf 6 [[3,4,5]]]

@[expose] def lat : List (List (Perm (Fin 6))) :=
  [L1, L2, L3]

@[expose] def reps : List (Perm (Fin 6) × ℕ × List (List ℕ)) :=
  [
    (permOf 6 [], 0, [[0],[1]]),
    (permOf 6 [[3,4,5]], 3, [[0],[1],[2]]),
    (permOf 6 [[2,4],[3,5]], 1, [[0],[1],[2]]),
    (permOf 6 [[1,2],[4,5]], 2, [[0],[1],[2]]),
    (permOf 6 [[1,2],[3,4]], 3, [[0],[1],[1,0,1,0,2,1,2,1,0,1]]),
    (permOf 6 [[1,2],[3,5]], 3, [[0],[1],[1,0,1,2,1,2,1,0,1,0]]),
    (permOf 6 [[1,2,4,3,5]], 3, [[0],[1],[0,2,2,1,0,2]]),
    (permOf 6 [[1,4,3,5,2]], 3, [[0],[1],[2,0,1,2,2,0]]),
    (permOf 6 [[1,4],[3,5]], 3, [[0],[1],[0,2,0,1,2,1,0,2]])]

@[expose] def joins : List (ℕ × ℕ × ℕ × List (List ℕ)) :=
  [
    (0, 0, 0, [[0],[1]]),
    (0, 1, 1, [[0],[1],[4]]),
    (0, 2, 2, [[0],[1],[4]]),
    (0, 3, 3, [[0],[1],[4]]),
    (1, 0, 1, [[0],[1],[2]]),
    (1, 1, 1, [[0],[1],[2]]),
    (1, 2, 3, [[0],[1],[1,2,5,2,1,0]]),
    (1, 3, 3, [[0],[1],[5]]),
    (2, 0, 2, [[0],[1],[2]]),
    (2, 1, 3, [[0],[1],[1,5,2,5,1,0]]),
    (2, 2, 2, [[0],[1],[2]]),
    (2, 3, 3, [[0],[1],[5]]),
    (3, 0, 3, [[0],[1],[2]]),
    (3, 1, 3, [[0],[1],[2]]),
    (3, 2, 3, [[0],[1],[2]]),
    (3, 3, 3, [[0],[1],[2]])]

@[expose] def sizes : List ℕ := [8, 24, 24, 360]

@[expose] def msize : ℕ := 360

@[expose] def cert : LatCert (Perm (Fin 6)) where
  depth := 64
  mGens := mGens
  tGens := tGens
  lat := lat
  reps := reps
  joins := joins
  sizes := sizes
  msize := msize

@[expose] def ct0 : CTCert (Perm (Fin 6)) where
  depth := 64
  hGens := tGens
  nGens := [permOf 6 [[0,3],[1,2]], permOf 6 [[2,3],[4,5]]]
  expo := 3

@[expose] def ct1 : CTCert (Perm (Fin 6)) where
  depth := 64
  hGens := L1
  nGens := [permOf 6 [[0,1],[2,3]], permOf 6 [[0,1],[4,5]]]
  expo := 2

@[expose] def ct2 : CTCert (Perm (Fin 6)) where
  depth := 64
  hGens := L2
  nGens := [permOf 6 [[0,3],[1,2]], permOf 6 [[0,1],[2,3]]]
  expo := 2

@[expose] def cts : List (CTCert (Perm (Fin 6))) := [ct0, ct1, ct2]

end CFSG.QuasithinUnique.L246C127.Even6
