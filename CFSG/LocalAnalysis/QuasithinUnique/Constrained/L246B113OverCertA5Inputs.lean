module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenCertDefs

public section

namespace CFSG.QuasithinUnique.Bridge.Over.CertA5
open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.L246C127

@[expose] def mGens : List (Perm (Fin 5)) :=
  [permOf 5 [[0,1,2]], permOf 5 [[0,1,2,3,4]]]

@[expose] def tGens : List (Perm (Fin 5)) :=
  [permOf 5 [[1,2],[3,4]], permOf 5 [[1,3],[2,4]]]

@[expose] def L1 : List (Perm (Fin 5)) :=
  [permOf 5 [[1,2],[3,4]], permOf 5 [[1,3],[2,4]], permOf 5 [[2,3,4]]]

@[expose] def L2 : List (Perm (Fin 5)) :=
  [permOf 5 [[1,2],[3,4]], permOf 5 [[1,3],[2,4]], permOf 5 [[0,1],[3,4]]]

@[expose] def lat : List (List (Perm (Fin 5))) :=
  [L1, L2]

@[expose] def reps : List (Perm (Fin 5) × ℕ × List (List ℕ)) :=
  [
    (permOf 5 [], 0, [[0],[1]]),
    (permOf 5 [[2,3,4]], 1, [[0],[1],[2]]),
    (permOf 5 [[2,4,3]], 1, [[0],[1],[2,2]]),
    (permOf 5 [[0,1],[3,4]], 2, [[0],[1],[2]]),
    (permOf 5 [[0,1],[2,3]], 2, [[0],[1],[0,2,1,2,0]]),
    (permOf 5 [[0,1],[2,4]], 2, [[0],[1],[0,2,1,0,2,0]])]

@[expose] def joins : List (ℕ × ℕ × ℕ × List (List ℕ)) :=
  [
    (0, 0, 0, [[0],[1]]),
    (0, 1, 1, [[0],[1],[4]]),
    (0, 2, 2, [[0],[1],[4]]),
    (1, 0, 1, [[0],[1],[2]]),
    (1, 1, 1, [[0],[1],[2]]),
    (1, 2, 2, [[0],[1],[5]]),
    (2, 0, 2, [[0],[1],[2]]),
    (2, 1, 2, [[0],[1],[2]]),
    (2, 2, 2, [[0],[1],[2]])]

@[expose] def sizes : List ℕ := [4, 12, 60]

@[expose] def msize : ℕ := 60

@[expose] def cert : LatCert (Perm (Fin 5)) where
  depth := 64
  mGens := mGens
  tGens := tGens
  lat := lat
  reps := reps
  joins := joins
  sizes := sizes
  msize := msize

@[expose] def ct0 : CTCert (Perm (Fin 5)) where
  depth := 64
  hGens := tGens
  nGens := [permOf 5 [[1,2],[3,4]], permOf 5 [[1,4],[2,3]]]
  expo := 2

@[expose] def ct1 : CTCert (Perm (Fin 5)) where
  depth := 64
  hGens := L1
  nGens := [permOf 5 [[1,3],[2,4]], permOf 5 [[1,2],[3,4]]]
  expo := 2

@[expose] def cts : List (CTCert (Perm (Fin 5))) := [ct0, ct1]

end CFSG.QuasithinUnique.Bridge.Over.CertA5
