module

public import CFSG.LieType.Ree.LargeReeInvolutionCoordinates

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeCover

@[expose] def aOneWord : Word :=
  [(24, [[]]), (33, [[]])]

@[expose] def cWord : Word :=
  [(28, [[]]), (30, [[]])]

@[expose] def lOneWord : Word :=
  [(41, [[]]), (45, [[]])]

@[expose] def zWord : Word :=
  [(44, [[24]]), (47, [[25]])]

@[expose] def vACoords : List Poly :=
  [[[], [0]],
   [[1]],
   [[1], [3]],
   [[13]],
   [[2]],
   [[2], [3, 13], [5]],
   [[1, 1, 13], [14]],
   [[1, 1, 13], [2, 3], [9], [14]],
   [[1, 1, 13], [3, 3, 13], [14], [19]],
   [[], [12]],
   [[12, 13], [15]],
   [[2, 12], [7]],
   [[2, 12], [3, 12, 13], [4], [5, 12], [7]],
   [[1, 1, 12, 13], [12, 14], [17]],
   [[1, 1, 12, 13], [2, 3, 12], [9, 12], [10], [12, 14], [17]],
   [[1, 1, 12, 13], [3, 3, 12, 13], [3, 3, 15], [12, 14], [12, 19], [16], [17]],
   [[1, 1, 12, 13, 13], [2, 2, 12], [12, 13, 14], [21]],
   [[1, 1, 12, 13, 13], [2, 2, 12], [2, 5, 12], [9, 12, 13], [9, 15], [11], [12, 13, 14], [21]],
   [[1, 1, 12, 13, 13], [2, 2, 12], [5, 5, 12], [12, 13, 14], [12, 13, 19], [15, 19], [21],
     [22]],
   [[1, 1, 3, 12, 13, 13], [1, 1, 5, 12, 13], [2, 2, 3, 12], [2, 9, 12], [3, 12, 13, 14],
     [5, 12, 14], [6], [7, 9]],
   [[1, 1, 3, 12, 13, 13], [1, 1, 5, 12, 13], [2, 2, 3, 12], [2, 3, 5, 12], [2, 9, 12],
     [2, 12, 19], [3, 9, 12, 13], [3, 12, 13, 14], [4, 9], [5, 9, 12], [5, 12, 14], [6], [7, 9],
     [7, 19], [8]],
   [[1, 1, 3, 3, 12, 13, 13], [1, 1, 12, 13, 19], [2, 2, 3, 3, 12], [3, 3, 12, 13, 14],
     [9, 9, 12], [12, 14, 19], [17, 19], [23]],
   [[1, 1, 5, 5, 12, 13], [1, 1, 12, 13, 13, 19], [2, 2, 12, 19], [5, 5, 12, 14], [5, 5, 17],
     [9, 9, 12, 13], [9, 9, 15], [12, 13, 14, 19], [18]],
   [[1, 1, 5, 5, 12, 12, 13], [1, 1, 5, 5, 12, 13], [1, 1, 12, 12, 13, 13, 19],
     [1, 1, 12, 13, 13, 16], [1, 1, 12, 13, 13, 19], [1, 1, 12, 13, 15, 19], [2, 2, 12, 12, 19],
     [2, 2, 12, 16], [2, 2, 12, 19], [5, 5, 12, 12, 14], [5, 5, 12, 14], [5, 5, 12, 17],
     [5, 5, 17], [9, 9, 12, 12, 13], [9, 9, 12, 13], [9, 9, 12, 15], [9, 9, 15],
     [12, 12, 13, 14, 19], [12, 13, 14, 16], [12, 13, 14, 19], [12, 13, 17, 19],
     [12, 14, 15, 19], [15, 17, 19], [18], [20]]]

@[expose] def avCoords : List Poly :=
  [[[], [0]],
   [[1]],
   [[3]],
   [[13]],
   [[2]],
   [[3, 13], [5]],
   [[1, 1, 13], [14]],
   [[2, 3], [9]],
   [[3, 3, 13], [19]],
   [[], [12]],
   [[12, 13], [13], [15]],
   [[2], [2, 12], [7]],
   [[3, 12, 13], [3, 13], [4], [5], [5, 12]],
   [[1, 1, 12, 13], [1, 1, 13], [12, 14], [14], [17]],
   [[2, 3], [2, 3, 12], [9], [9, 12], [10]],
   [[3, 3, 12, 13], [3, 3, 13], [3, 3, 15], [12, 19], [16], [19]],
   [[1, 1, 12, 13, 13], [1, 1, 13, 13], [2, 2], [2, 2, 12], [12, 13, 14], [13, 14], [21]],
   [[2, 5], [2, 5, 12], [9, 12, 13], [9, 13], [9, 15], [11]],
   [[5, 5], [5, 5, 12], [12, 13, 19], [13, 19], [15, 19], [22]],
   [[1, 1, 3, 12, 13, 13], [1, 1, 3, 13, 13], [1, 1, 5, 12, 13], [1, 1, 5, 13], [2, 2, 3],
     [2, 2, 3, 12], [2, 9], [2, 9, 12], [3, 12, 13, 14], [3, 13, 14], [5, 12, 14], [5, 14], [6],
     [7, 9]],
   [[2, 3, 5], [2, 3, 5, 12], [2, 12, 19], [2, 19], [3, 9, 12, 13], [3, 9, 13], [4, 9], [5, 9],
     [5, 9, 12], [7, 19], [8]],
   [[1, 1, 3, 3, 12, 13, 13], [1, 1, 3, 3, 13, 13], [1, 1, 12, 13, 19], [1, 1, 13, 19],
     [2, 2, 3, 3], [2, 2, 3, 3, 12], [3, 3, 12, 13, 14], [3, 3, 13, 14], [9, 9], [9, 9, 12],
     [12, 14, 19], [14, 19], [17, 19], [23]],
   [[1, 1, 5, 5, 12, 13], [1, 1, 5, 5, 13], [1, 1, 12, 13, 13, 19], [1, 1, 13, 13, 19],
     [2, 2, 12, 19], [2, 2, 19], [5, 5, 12, 14], [5, 5, 14], [5, 5, 17], [9, 9, 12, 13],
     [9, 9, 13], [9, 9, 15], [12, 13, 14, 19], [13, 14, 19], [18]],
   [[1, 1, 5, 5, 12, 12, 13], [1, 1, 5, 5, 13], [1, 1, 12, 12, 13, 13, 19],
     [1, 1, 12, 13, 13, 16], [1, 1, 12, 13, 15, 19], [1, 1, 13, 13, 16], [1, 1, 13, 13, 19],
     [1, 1, 13, 15, 19], [2, 2, 12, 12, 19], [2, 2, 12, 16], [2, 2, 16], [2, 2, 19],
     [5, 5, 12, 12, 14], [5, 5, 12, 17], [5, 5, 14], [5, 5, 17], [9, 9, 12, 12, 13],
     [9, 9, 12, 15], [9, 9, 13], [9, 9, 15], [12, 12, 13, 14, 19], [12, 13, 14, 16],
     [12, 13, 17, 19], [12, 14, 15, 19], [13, 14, 16], [13, 14, 19], [13, 17, 19], [14, 15, 19],
     [15, 17, 19], [20]]]

@[expose] def vCCoords : List Poly :=
  [[[0]],
   [[1]],
   [[3]],
   [[13]],
   [[], [2]],
   [[3, 13], [5]],
   [[], [1, 1, 13], [14]],
   [[2, 3], [9]],
   [[3, 3, 13], [19]],
   [[12]],
   [[12, 13], [15]],
   [[2, 12], [7], [12]],
   [[3, 12, 13], [4], [5, 12]],
   [[1, 1, 12, 13], [12], [12, 14], [17]],
   [[2, 3, 12], [9, 12], [10]],
   [[3, 3, 12, 13], [3, 3, 15], [12, 19], [16]],
   [[1, 1, 12, 13, 13], [2, 2, 12], [12], [12, 13], [12, 13, 14], [15], [21]],
   [[2, 5, 12], [3, 12, 13], [4], [5, 12], [9, 12, 13], [9, 15], [11]],
   [[5, 5, 12], [12, 13, 19], [15, 19], [22]],
   [[1, 1, 3, 12, 13, 13], [1, 1, 5, 12, 13], [2, 2, 3, 12], [2, 3, 12], [2, 9, 12],
     [3, 12, 13], [3, 12, 13, 14], [4], [5, 12], [5, 12, 14], [6], [7, 9], [9, 12], [10]],
   [[2, 3, 5, 12], [2, 12, 19], [3, 3, 12, 13], [3, 3, 15], [3, 9, 12, 13], [4, 9], [5, 9, 12],
     [7, 19], [8], [12, 19], [16]],
   [[1, 1, 3, 3, 12, 13, 13], [1, 1, 12, 13, 19], [2, 2, 3, 3, 12], [3, 3, 12, 13],
     [3, 3, 12, 13, 14], [3, 3, 15], [9, 9, 12], [12, 14, 19], [12, 19], [16], [17, 19], [23]],
   [[1, 1, 5, 5, 12, 13], [1, 1, 12, 13, 13, 19], [2, 2, 12, 19], [3, 3, 12, 13], [3, 3, 15],
     [5, 5, 12], [5, 5, 12, 14], [5, 5, 17], [9, 9, 12, 13], [9, 9, 15], [12, 13, 14, 19],
     [12, 13, 19], [12, 19], [15, 19], [16], [18], [22]],
   [[1, 1, 5, 5, 12, 12, 13], [1, 1, 12, 12, 13, 13, 19], [1, 1, 12, 13, 13, 16],
     [1, 1, 12, 13, 15, 19], [2, 2, 12, 12, 19], [2, 2, 12, 16], [3, 3, 12, 12, 13],
     [3, 3, 12, 15], [3, 3, 15, 15], [4, 4], [5, 5, 12, 12], [5, 5, 12, 12, 14], [5, 5, 12, 17],
     [9, 9, 12, 12, 13], [9, 9, 12, 15], [12, 12, 13, 14, 19], [12, 12, 13, 19], [12, 12, 19],
     [12, 13, 14, 16], [12, 13, 16], [12, 13, 17, 19], [12, 14, 15, 19], [12, 15, 19], [12, 16],
     [15, 16], [15, 17, 19], [20]]]

@[expose] def cvCoords : List Poly :=
  [[[0]],
   [[1]],
   [[3]],
   [[13]],
   [[], [2]],
   [[0], [3, 13], [5]],
   [[], [1, 1, 13], [14]],
   [[0], [0, 1], [2, 3], [3], [9]],
   [[0, 0], [3, 3, 13], [19]],
   [[12]],
   [[12, 13], [15]],
   [[2, 12], [7]],
   [[3, 12, 13], [4], [5, 12]],
   [[1, 1, 12, 13], [12, 14], [17]],
   [[2, 3, 12], [9, 12], [10]],
   [[3, 3, 12, 13], [3, 3, 15], [12, 19], [16]],
   [[1, 1, 12, 13, 13], [2, 2, 12], [12, 13, 14], [21]],
   [[2, 5, 12], [9, 12, 13], [9, 15], [11]],
   [[5, 5, 12], [12, 13, 19], [15, 19], [22]],
   [[1, 1, 3, 12, 13, 13], [1, 1, 5, 12, 13], [2, 2, 3, 12], [2, 9, 12], [3, 12, 13, 14],
     [5, 12, 14], [6], [7, 9]],
   [[2, 3, 5, 12], [2, 12, 19], [3, 9, 12, 13], [4, 9], [5, 9, 12], [7, 19], [8]],
   [[1, 1, 3, 3, 12, 13, 13], [1, 1, 12, 13, 19], [2, 2, 3, 3, 12], [3, 3, 12, 13, 14],
     [9, 9, 12], [12, 14, 19], [17, 19], [23]],
   [[1, 1, 5, 5, 12, 13], [1, 1, 12, 13, 13, 19], [2, 2, 12, 19], [5, 5, 12, 14], [5, 5, 17],
     [9, 9, 12, 13], [9, 9, 15], [12, 13, 14, 19], [18]],
   [[1, 1, 5, 5, 12, 12, 13], [1, 1, 12, 12, 13, 13, 19], [1, 1, 12, 13, 13, 16],
     [1, 1, 12, 13, 15, 19], [2, 2, 12, 12, 19], [2, 2, 12, 16], [5, 5, 12, 12, 14],
     [5, 5, 12, 17], [9, 9, 12, 12, 13], [9, 9, 12, 15], [12, 12, 13, 14, 19], [12, 13, 14, 16],
     [12, 13, 17, 19], [12, 14, 15, 19], [15, 17, 19], [20]]]

@[expose] def czvCoords : List Poly :=
  [[[0]],
   [[1]],
   [[3]],
   [[13]],
   [[], [2]],
   [[0], [3, 13], [5]],
   [[], [1, 1, 13], [14]],
   [[0], [0, 1], [2, 3], [3], [9]],
   [[0, 0], [3, 3, 13], [19]],
   [[12]],
   [[12, 13], [15]],
   [[2, 12], [7]],
   [[3, 12, 13], [4], [5, 12]],
   [[1, 1, 12, 13], [12, 14], [17]],
   [[2, 3, 12], [9, 12], [10]],
   [[3, 3, 12, 13], [3, 3, 15], [12, 19], [16]],
   [[1, 1, 12, 13, 13], [2, 2, 12], [12, 13, 14], [21]],
   [[2, 5, 12], [9, 12, 13], [9, 15], [11]],
   [[5, 5, 12], [12, 13, 19], [15, 19], [22]],
   [[1, 1, 3, 12, 13, 13], [1, 1, 5, 12, 13], [2, 2, 3, 12], [2, 9, 12], [3, 12, 13, 14],
     [5, 12, 14], [6], [7, 9]],
   [[2, 3, 5, 12], [2, 12, 19], [3, 9, 12, 13], [4, 9], [5, 9, 12], [7, 19], [8], [24]],
   [[1, 1, 3, 3, 12, 13, 13], [1, 1, 12, 13, 19], [2, 2, 3, 3, 12], [3, 3, 12, 13, 14],
     [9, 9, 12], [12, 14, 19], [17, 19], [23]],
   [[1, 1, 5, 5, 12, 13], [1, 1, 12, 13, 13, 19], [2, 2, 12, 19], [5, 5, 12, 14], [5, 5, 17],
     [9, 9, 12, 13], [9, 9, 15], [12, 13, 14, 19], [18]],
   [[1, 1, 5, 5, 12, 12, 13], [1, 1, 12, 12, 13, 13, 19], [1, 1, 12, 13, 13, 16],
     [1, 1, 12, 13, 15, 19], [2, 2, 12, 12, 19], [2, 2, 12, 16], [5, 5, 12, 12, 14],
     [5, 5, 12, 17], [9, 9, 12, 12, 13], [9, 9, 12, 15], [12, 12, 13, 14, 19], [12, 13, 14, 16],
     [12, 13, 17, 19], [12, 14, 15, 19], [15, 17, 19], [20], [25]]]

@[expose] def vLCoords : List Poly :=
  [[[0]],
   [[1]],
   [[3]],
   [[13]],
   [[2]],
   [[3, 13], [5]],
   [[1, 1, 13], [14]],
   [[2, 3], [9]],
   [[3, 3, 13], [19]],
   [[12]],
   [[12, 13], [15]],
   [[2, 12], [7]],
   [[3, 12, 13], [4], [5, 12]],
   [[1, 1, 12, 13], [12, 14], [17]],
   [[2, 3, 12], [9, 12], [10]],
   [[3, 3, 12, 13], [3, 3, 15], [12, 19], [16]],
   [[1, 1, 12, 13, 13], [2, 2, 12], [12, 13, 14], [21]],
   [[], [2, 5, 12], [9, 12, 13], [9, 15], [11]],
   [[5, 5, 12], [12, 13, 19], [15, 19], [22]],
   [[1, 1, 3, 12, 13, 13], [1, 1, 5, 12, 13], [2, 2, 3, 12], [2, 9, 12], [3, 12, 13, 14],
     [5, 12, 14], [6], [7, 9]],
   [[2, 3, 5, 12], [2, 12, 19], [3, 9, 12, 13], [4, 9], [5, 9, 12], [7, 19], [8]],
   [[], [1, 1, 3, 3, 12, 13, 13], [1, 1, 12, 13, 19], [2, 2, 3, 3, 12], [3, 3, 12, 13, 14],
     [9, 9, 12], [12, 14, 19], [17, 19], [23]],
   [[1, 1, 5, 5, 12, 13], [1, 1, 12, 13, 13, 19], [2, 2, 12, 19], [5, 5, 12, 14], [5, 5, 17],
     [9, 9, 12, 13], [9, 9, 15], [12, 13, 14, 19], [18]],
   [[1, 1, 5, 5, 12, 12, 13], [1, 1, 12, 12, 13, 13, 19], [1, 1, 12, 13, 13, 16],
     [1, 1, 12, 13, 15, 19], [2, 2, 12, 12, 19], [2, 2, 12, 16], [5, 5, 12, 12, 14],
     [5, 5, 12, 17], [9, 9, 12, 12, 13], [9, 9, 12, 15], [12, 12, 13, 14, 19], [12, 13, 14, 16],
     [12, 13, 17, 19], [12, 14, 15, 19], [15, 17, 19], [20]]]

@[expose] def lvCoords : List Poly :=
  [[[0]],
   [[1]],
   [[3]],
   [[13]],
   [[2]],
   [[3, 13], [5]],
   [[1, 1, 13], [14]],
   [[2, 3], [9]],
   [[3, 3, 13], [19]],
   [[12]],
   [[12, 13], [15]],
   [[2, 12], [7]],
   [[3, 12, 13], [4], [5, 12]],
   [[1, 1, 12, 13], [12, 14], [17]],
   [[2, 3, 12], [9, 12], [10]],
   [[3, 3, 12, 13], [3, 3, 15], [12, 19], [16]],
   [[1, 1, 12, 13, 13], [2, 2, 12], [12, 13, 14], [21]],
   [[], [2, 5, 12], [9, 12, 13], [9, 15], [11]],
   [[5, 5, 12], [12, 13, 19], [15, 19], [22]],
   [[1], [1, 1, 3, 12, 13, 13], [1, 1, 5, 12, 13], [2, 2, 3, 12], [2, 9, 12], [3, 12, 13, 14],
     [5, 12, 14], [6], [7, 9]],
   [[2, 3, 5, 12], [2, 12, 19], [3], [3, 9, 12, 13], [4, 9], [5, 9, 12], [7, 19], [8]],
   [[], [1, 1, 3, 3, 12, 13, 13], [1, 1, 12, 13, 19], [2, 2, 3, 3, 12], [3, 3, 12, 13, 14],
     [9, 9, 12], [12, 14, 19], [17, 19], [23]],
   [[1, 1, 5, 5, 12, 13], [1, 1, 12, 13, 13, 19], [2, 2, 12, 19], [5, 5, 12, 14], [5, 5, 17],
     [9, 9, 12, 13], [9, 9, 15], [12, 13, 14, 19], [13], [18]],
   [[1, 1, 5, 5, 12, 12, 13], [1, 1, 12, 12, 13, 13, 19], [1, 1, 12, 13, 13, 16],
     [1, 1, 12, 13, 15, 19], [2, 2, 12, 12, 19], [2, 2, 12, 16], [5, 5, 12, 12, 14],
     [5, 5, 12, 17], [9, 9, 12, 12, 13], [9, 9, 12, 15], [12, 12, 13, 14, 19], [12, 13, 14, 16],
     [12, 13, 17, 19], [12, 14, 15, 19], [15], [15, 17, 19], [20]]]

theorem vACoords_check : collectCheck 6000 (sylowWord ++ aOneWord) vACoords = true := by
  decide +kernel

theorem avCoords_check : collectCheck 6000 (aOneWord ++ sylowWord) avCoords = true := by
  decide +kernel

theorem vCCoords_check : collectCheck 6000 (sylowWord ++ cWord) vCCoords = true := by
  decide +kernel

theorem cvCoords_check : collectCheck 6000 (cWord ++ sylowWord) cvCoords = true := by
  decide +kernel

theorem czvCoords_check : collectCheck 6000 (cWord ++ zWord ++ sylowWord) czvCoords = true := by
  decide +kernel

theorem vLCoords_check : collectCheck 6000 (sylowWord ++ lOneWord) vLCoords = true := by
  decide +kernel

theorem lvCoords_check : collectCheck 6000 (lOneWord ++ sylowWord) lvCoords = true := by
  decide +kernel

section Centralizers

variable {m : ℕ} {K : Type} [Field K]

theorem sylowA_one_eq_wordEval
    (x : ℕ → K) : sylowA m K 1 = wordEval K x aOneWord := by
  simp [sylowA, sylowX, wordEval, aOneWord, polyEval, monoEval, largeReeSigma_one]

theorem sylowB_zero_one_eq_wordEval
    (x : ℕ → K) : sylowB m K 0 1 = wordEval K x cWord := by
  simp [sylowB, sylowX, wordEval, cWord, polyEval, monoEval, largeReeSigma_zero,
    largeReeSigma_one, pinnedX_zero]

theorem sylowL_one_eq_wordEval
    (x : ℕ → K) : sylowL m K 1 = wordEval K x lOneWord := by
  simp [sylowL, sylowX, wordEval, lOneWord, polyEval, monoEval, largeReeSigma_one]

theorem sylowH_zero_eq_wordEval
    {x : ℕ → K} {i : K} (h24 : x 24 = i)
    (h25 : x 25 = largeReeSigma m i) : sylowH m K 0 i = wordEval K x zWord := by
  simp [sylowH, sylowX, wordEval, zWord, polyEval, monoEval, largeReeSigma_zero, pinnedX_zero,
    h24, h25]

variable [CharP K F4.prime]

theorem polyEval_polyAdd_eq_zero {x : ℕ → K} {P Q : Poly} (h : polyEval x P = polyEval x Q) :
    polyEval x (polyAdd P Q) = 0 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [polyEval_polyAdd, h, CharTwo.add_self_eq_zero]

theorem sylowV_commute_sylowA_one_iff
    (a b c d e f g h i j k l : K) :
    sylowV m K a b c d e f g h i j k l * sylowA m K 1 =
        sylowA m K 1 * sylowV m K a b c d e f g h i j k l ↔
      b = 0 ∧ c = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0 ∧ j = 0 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  set x := coordVal m a b c d e f g h i j k l with hx
  rw [sylowV_eq_wordEval, sylowA_one_eq_wordEval x, ← wordEval_append, ← wordEval_append,
    wordEval_eq_iff vACoords_check avCoords_check]
  constructor
  · intro hc
    have hd : ∀ n : Fin 24, polyEval x (polyAdd (vACoords.getD n []) (avCoords.getD n [])) = 0 :=
      fun n => polyEval_polyAdd_eq_zero (hc n)
    have h26 : polyEval x (polyAdd (vACoords.getD 2 []) (avCoords.getD 2 [])) = 0 := hd 2
    have h29 : polyEval x (polyAdd (vACoords.getD 5 []) (avCoords.getD 5 [])) = 0 := hd 5
    rw [show polyAdd (vACoords.getD 2 []) (avCoords.getD 2 []) = [[1]] by decide +kernel] at h26
    rw [show polyAdd (vACoords.getD 5 []) (avCoords.getD 5 []) = [[2]] by decide +kernel] at h29
    simp only [polyEval, monoEval, hx, coordVal, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero] at h26 h29
    have hL : ∀ e ∈ ([(1, []), (13, []), (2, []), (14, [])] : List (ℕ × Poly)),
        polyEval x e.2 = x e.1 := by
      simp [polyEval, hx, coordVal, h26, h29, largeReeSigma_zero]
    have h36 : polyEval x (polyAdd (vACoords.getD 12 []) (avCoords.getD 12 [])) = 0 := hd 12
    have h38 : polyEval x (polyAdd (vACoords.getD 14 []) (avCoords.getD 14 [])) = 0 := hd 14
    have h41 : polyEval x (polyAdd (vACoords.getD 17 []) (avCoords.getD 17 [])) = 0 := hd 17
    rw [polyEval_eq_of_polySubst hL (q := [[5], [7]]) (by decide +kernel)] at h36
    rw [polyEval_eq_of_polySubst hL (q := [[9], [17]]) (by decide +kernel)] at h38
    rw [polyEval_eq_of_polySubst hL (q := [[21]]) (by decide +kernel)] at h41
    simp only [polyEval, monoEval, hx, coordVal, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero] at h36 h38 h41
    have hj : j = 0 := (largeReeSigma_eq_zero_iff j).1 h41
    have hf : f = 0 := by
      rw [hj, zero_add] at h38
      exact (largeReeSigma_eq_zero_iff f).1 h38
    have hh : h = 0 := by
      rw [hf, zero_add] at h36
      exact h36
    have hL' : ∀ e ∈ ([(1, []), (13, []), (2, []), (14, []), (5, []), (17, []), (7, []), (19, []),
        (9, []), (21, [])] : List (ℕ × Poly)), polyEval x e.2 = x e.1 := by
      simp [polyEval, hx, coordVal, h26, h29, hf, hh, hj, largeReeSigma_zero]
    have h44 : polyEval x (polyAdd (vACoords.getD 20 []) (avCoords.getD 20 [])) = 0 := hd 20
    rw [polyEval_eq_of_polySubst hL' (q := [[6]]) (by decide +kernel)] at h44
    simp only [polyEval, monoEval, hx, coordVal, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero] at h44
    exact ⟨h26, h29, hf, h44, hh, hj⟩
  · rintro ⟨hb, hc, hf, hg, hh, hj⟩ n
    have hL : ∀ e ∈ ([(1, []), (13, []), (2, []), (14, []), (5, []), (17, []), (6, []), (18, []),
        (7, []), (19, []), (9, []), (21, [])] : List (ℕ × Poly)), polyEval x e.2 = x e.1 := by
      simp [polyEval, hx, coordVal, hb, hc, hf, hg, hh, hj, largeReeSigma_zero]
    have hall : ∀ n : Fin 24, polySubst (substOf [(1, []), (13, []), (2, []), (14, []), (5, []),
        (17, []), (6, []), (18, []), (7, []), (19, []), (9, []), (21, [])])
          (polyAdd (vACoords.getD n []) (avCoords.getD n [])) = [] := by
      decide +kernel
    have h0 := polyEval_eq_of_polySubst hL (hall n)
    rw [polyEval_polyAdd] at h0
    exact eq_of_add_eq_zero_two h0

theorem sylowV_commute_sylowB_iff
    (a b c d e f g h i j k l : K) :
    sylowV m K a b c d e f g h i j k l * sylowB m K 0 1 =
        sylowB m K 0 1 * sylowV m K a b c d e f g h i j k l ↔
      a = 0 ∧ d = 0 ∧ e = 0 ∧ k = 0 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  set x := coordVal m a b c d e f g h i j k l with hx
  rw [sylowV_eq_wordEval, sylowB_zero_one_eq_wordEval x, ← wordEval_append, ← wordEval_append,
    wordEval_eq_iff vCCoords_check cvCoords_check]
  constructor
  · intro hc
    have hd : ∀ n : Fin 24, polyEval x (polyAdd (vCCoords.getD n []) (cvCoords.getD n [])) = 0 :=
      fun n => polyEval_polyAdd_eq_zero (hc n)
    have h29 : polyEval x (polyAdd (vCCoords.getD 5 []) (cvCoords.getD 5 [])) = 0 := hd 5
    rw [show polyAdd (vCCoords.getD 5 []) (cvCoords.getD 5 []) = [[0]] by decide +kernel] at h29
    simp only [polyEval, monoEval, hx, coordVal, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero] at h29
    have h31 : polyEval x (polyAdd (vCCoords.getD 7 []) (cvCoords.getD 7 [])) = 0 := hd 7
    rw [polyEval_eq_of_polySubst (l := [(0, []), (12, [])])
      (by simp [polyEval, hx, coordVal, h29, largeReeSigma_zero]) (q := [[3]])
      (by decide +kernel)] at h31
    simp only [polyEval, monoEval, hx, coordVal, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero] at h31
    have hL : ∀ e ∈ ([(0, []), (12, []), (3, []), (15, [])] : List (ℕ × Poly)),
        polyEval x e.2 = x e.1 := by
      simp [polyEval, hx, coordVal, h29, h31, largeReeSigma_zero]
    have h41 : polyEval x (polyAdd (vCCoords.getD 17 []) (cvCoords.getD 17 [])) = 0 := hd 17
    have h43 : polyEval x (polyAdd (vCCoords.getD 19 []) (cvCoords.getD 19 [])) = 0 := hd 19
    rw [polyEval_eq_of_polySubst hL (q := [[4]]) (by decide +kernel)] at h41
    rw [polyEval_eq_of_polySubst hL (q := [[4], [10]]) (by decide +kernel)] at h43
    simp only [polyEval, monoEval, hx, coordVal, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero] at h41 h43
    rw [h41, zero_add] at h43
    exact ⟨h29, h31, h41, h43⟩
  · rintro ⟨ha, hd, he, hk⟩ n
    have hL : ∀ e ∈ ([(0, []), (12, []), (3, []), (15, []), (4, []), (16, []), (10, []),
        (22, [])] : List (ℕ × Poly)), polyEval x e.2 = x e.1 := by
      simp [polyEval, hx, coordVal, ha, hd, he, hk, largeReeSigma_zero]
    have hall : ∀ n : Fin 24, polySubst (substOf [(0, []), (12, []), (3, []), (15, []), (4, []),
        (16, []), (10, []), (22, [])])
          (polyAdd (vCCoords.getD n []) (cvCoords.getD n [])) = [] := by
      decide +kernel
    have h0 := polyEval_eq_of_polySubst hL (hall n)
    rw [polyEval_polyAdd] at h0
    exact eq_of_add_eq_zero_two h0

theorem sylowV_commute_sylowL_one_iff
    (a b c d e f g h i j k l : K) :
    sylowV m K a b c d e f g h i j k l * sylowL m K 1 =
        sylowL m K 1 * sylowV m K a b c d e f g h i j k l ↔ b = 0 ∧ d = 0 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  set x := coordVal m a b c d e f g h i j k l with hx
  rw [sylowV_eq_wordEval, sylowL_one_eq_wordEval x, ← wordEval_append, ← wordEval_append,
    wordEval_eq_iff vLCoords_check lvCoords_check]
  constructor
  · intro hc
    have h43 : polyEval x (polyAdd (vLCoords.getD 19 []) (lvCoords.getD 19 [])) = 0 :=
      polyEval_polyAdd_eq_zero (hc 19)
    have h44 : polyEval x (polyAdd (vLCoords.getD 20 []) (lvCoords.getD 20 [])) = 0 :=
      polyEval_polyAdd_eq_zero (hc 20)
    rw [show polyAdd (vLCoords.getD 19 []) (lvCoords.getD 19 []) = [[1]] by decide +kernel] at h43
    rw [show polyAdd (vLCoords.getD 20 []) (lvCoords.getD 20 []) = [[3]] by decide +kernel] at h44
    simp only [polyEval, monoEval, hx, coordVal, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero] at h43 h44
    exact ⟨h43, h44⟩
  · rintro ⟨hb, hd⟩ n
    have hL : ∀ e ∈ ([(1, []), (13, []), (3, []), (15, [])] : List (ℕ × Poly)),
        polyEval x e.2 = x e.1 := by
      simp [polyEval, hx, coordVal, hb, hd, largeReeSigma_zero]
    have hall : ∀ n : Fin 24, polySubst (substOf [(1, []), (13, []), (3, []), (15, [])])
        (polyAdd (vLCoords.getD n []) (lvCoords.getD n [])) = [] := by
      decide +kernel
    have h0 := polyEval_eq_of_polySubst hL (hall n)
    rw [polyEval_polyAdd] at h0
    exact eq_of_add_eq_zero_two h0

@[expose] def coordValZ (m : ℕ) (a b c d e f g h i j k l z : K) : ℕ → K
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => e
  | 5 => f
  | 6 => g
  | 7 => h
  | 8 => i
  | 9 => j
  | 10 => k
  | 11 => l
  | 12 => largeReeSigma m a
  | 13 => largeReeSigma m b
  | 14 => largeReeSigma m c
  | 15 => largeReeSigma m d
  | 16 => largeReeSigma m e
  | 17 => largeReeSigma m f
  | 18 => largeReeSigma m g
  | 19 => largeReeSigma m h
  | 20 => largeReeSigma m i
  | 21 => largeReeSigma m j
  | 22 => largeReeSigma m k
  | 23 => largeReeSigma m l
  | 24 => z
  | 25 => largeReeSigma m z
  | _ => 0

omit [CharP K F4.prime] in
theorem sylowV_eq_wordEvalZ
    (a b c d e f g h i j k l z : K) :
    sylowV m K a b c d e f g h i j k l =
      wordEval K (coordValZ m a b c d e f g h i j k l z) sylowWord := by
  simp only [sylowV, sylowA, sylowB, sylowD, sylowF, sylowH, sylowJ, sylowK, sylowL,
    sylowX, wordEval, sylowWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, polyEval, monoEval, List.sum_cons, List.sum_nil, add_zero, coordValZ, mul_assoc]
  ring_nf

theorem sylowV_conj_eq_of_mem_mul
    (a b c d e f g h i j k l z : K)
    (hz : sylowV m K a b c d e f g h i j k l * sylowB m K 0 1 *
        (sylowV m K a b c d e f g h i j k l)⁻¹ = sylowB m K 0 1 * sylowH m K 0 z) :
    sylowV m K a b c d e f g h i j k l * sylowB m K 0 1 *
        (sylowV m K a b c d e f g h i j k l)⁻¹ = sylowB m K 0 1 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  set y := coordValZ m a b c d e f g h i j k l z with hy
  have hz' : sylowV m K a b c d e f g h i j k l * sylowB m K 0 1 =
      sylowB m K 0 1 * sylowH m K 0 z * sylowV m K a b c d e f g h i j k l := by
    rw [← hz]
    group
  rw [sylowV_eq_wordEvalZ _ _ _ _ _ _ _ _ _ _ _ _ z, sylowB_zero_one_eq_wordEval y,
    sylowH_zero_eq_wordEval (x := y) (i := z) rfl rfl, ← wordEval_append, ← wordEval_append,
    ← wordEval_append, wordEval_eq_iff vCCoords_check czvCoords_check] at hz'
  have hd : ∀ n : Fin 24, polyEval y (polyAdd (vCCoords.getD n []) (czvCoords.getD n [])) = 0 :=
    fun n => polyEval_polyAdd_eq_zero (hz' n)
  have h29 : polyEval y (polyAdd (vCCoords.getD 5 []) (czvCoords.getD 5 [])) = 0 := hd 5
  rw [show polyAdd (vCCoords.getD 5 []) (czvCoords.getD 5 []) = [[0]] by decide +kernel] at h29
  simp only [polyEval, monoEval, hy, coordValZ, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero] at h29
  have h31 : polyEval y (polyAdd (vCCoords.getD 7 []) (czvCoords.getD 7 [])) = 0 := hd 7
  rw [polyEval_eq_of_polySubst (l := [(0, []), (12, [])])
    (by simp [polyEval, hy, coordValZ, h29, largeReeSigma_zero]) (q := [[3]])
    (by decide +kernel)] at h31
  simp only [polyEval, monoEval, hy, coordValZ, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero] at h31
  have hL : ∀ e ∈ ([(0, []), (12, []), (3, []), (15, [])] : List (ℕ × Poly)),
      polyEval y e.2 = y e.1 := by
    simp [polyEval, hy, coordValZ, h29, h31, largeReeSigma_zero]
  have h41 : polyEval y (polyAdd (vCCoords.getD 17 []) (czvCoords.getD 17 [])) = 0 := hd 17
  have h43 : polyEval y (polyAdd (vCCoords.getD 19 []) (czvCoords.getD 19 [])) = 0 := hd 19
  rw [polyEval_eq_of_polySubst hL (q := [[4]]) (by decide +kernel)] at h41
  rw [polyEval_eq_of_polySubst hL (q := [[4], [10]]) (by decide +kernel)] at h43
  simp only [polyEval, monoEval, hy, coordValZ, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero] at h41 h43
  rw [h41, zero_add] at h43
  have hcomm := (sylowV_commute_sylowB_iff (m := m) a b c d e f g h i j k l).2
    ⟨h29, h31, h41, h43⟩
  rw [hcomm]
  group

end Centralizers

end CFSG.LieType.Ree.LargeReeInvolution
