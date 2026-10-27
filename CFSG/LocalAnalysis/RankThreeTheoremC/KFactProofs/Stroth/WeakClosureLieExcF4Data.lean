module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcFpf

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice

namespace F4Data

@[expose] def coxPow (k : ℕ) : List (Fin Tag.F4.rank) := (List.replicate k [0, 1, 2, 3]).flatten

@[expose] def r12a : List (Fin Tag.F4.rank) :=
  [2, 1, 2, 0, 1, 2]

@[expose] def r12b : List (Fin Tag.F4.rank) :=
  [2, 1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 3, 1, 2, 0, 1, 0]

@[expose] def r12c : List (Fin Tag.F4.rank) :=
  [2, 1, 2, 3, 2, 1, 2, 0, 1, 2, 3, 2, 0, 1, 2, 1, 0]

@[expose] def r12d : List (Fin Tag.F4.rank) :=
  [2, 1, 2, 0, 1, 2, 3, 2, 1, 2, 0]

theorem r12_dc : wordMat Tag.F4 (cw (cw r12a r12b) (cw r12c r12d)) = -1 := by decide +kernel

@[expose] def r3a : List (Fin Tag.F4.rank) :=
  [2, 3, 1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 0, 1]

@[expose] def r3b : List (Fin Tag.F4.rank) :=
  [1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 3, 2]

@[expose] def r3c : List (Fin Tag.F4.rank) :=
  [2, 1, 2, 0, 1, 2, 3, 1, 2, 0, 1, 2]

@[expose] def r3d : List (Fin Tag.F4.rank) :=
  [1, 2, 3, 2, 1, 2, 0, 1, 2, 3, 1, 2, 0, 1, 2, 1]

theorem r3_comm_a : wordMat Tag.F4 r3a * wordMat Tag.F4 (coxPow 4) = wordMat Tag.F4 (coxPow 4) * wordMat Tag.F4 r3a := by decide +kernel

theorem r3_comm_b : wordMat Tag.F4 r3b * wordMat Tag.F4 (coxPow 4) = wordMat Tag.F4 (coxPow 4) * wordMat Tag.F4 r3b := by decide +kernel

theorem r3_comm_c : wordMat Tag.F4 r3c * wordMat Tag.F4 (coxPow 4) = wordMat Tag.F4 (coxPow 4) * wordMat Tag.F4 r3c := by decide +kernel

theorem r3_comm_d : wordMat Tag.F4 r3d * wordMat Tag.F4 (coxPow 4) = wordMat Tag.F4 (coxPow 4) * wordMat Tag.F4 r3d := by decide +kernel

theorem r3_dc : wordMat Tag.F4 (cw (cw r3a r3b) (cw r3c r3d)) = (-1 : ℤ) • wordMat Tag.F4 (coxPow 4) ^ 0 := by decide +kernel

@[expose] def r4a : List (Fin Tag.F4.rank) :=
  [2, 3, 1, 2, 0, 1, 2, 0]

@[expose] def r4b : List (Fin Tag.F4.rank) :=
  [3, 2, 0, 1, 2, 3, 2, 0, 1, 2, 0, 1]

@[expose] def r4c : List (Fin Tag.F4.rank) :=
  [3, 2, 1, 0]

@[expose] def r4d : List (Fin Tag.F4.rank) :=
  [2, 3, 1, 2, 0, 1, 2, 3, 2, 0, 1, 0]

theorem r4_comm_a : wordMat Tag.F4 r4a * wordMat Tag.F4 (coxPow 3) = wordMat Tag.F4 (coxPow 3) * wordMat Tag.F4 r4a := by decide +kernel

theorem r4_comm_b : wordMat Tag.F4 r4b * wordMat Tag.F4 (coxPow 3) = wordMat Tag.F4 (coxPow 3) * wordMat Tag.F4 r4b := by decide +kernel

theorem r4_comm_c : wordMat Tag.F4 r4c * wordMat Tag.F4 (coxPow 3) = wordMat Tag.F4 (coxPow 3) * wordMat Tag.F4 r4c := by decide +kernel

theorem r4_comm_d : wordMat Tag.F4 r4d * wordMat Tag.F4 (coxPow 3) = wordMat Tag.F4 (coxPow 3) * wordMat Tag.F4 r4d := by decide +kernel

theorem r4_dc : wordMat Tag.F4 (cw (cw r4a r4b) (cw r4c r4d)) = (1 : ℤ) • wordMat Tag.F4 (coxPow 3) ^ 2 := by decide +kernel

@[expose] def r6a : List (Fin Tag.F4.rank) :=
  [2, 0, 1, 2]

@[expose] def r6b : List (Fin Tag.F4.rank) :=
  [1, 2, 3, 2, 1, 2, 0, 1, 2, 3, 2, 0, 1, 2, 1, 0]

@[expose] def r6c : List (Fin Tag.F4.rank) :=
  [2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 0]

@[expose] def r6d : List (Fin Tag.F4.rank) :=
  [2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 1, 0]

theorem r6_comm_a : wordMat Tag.F4 r6a * wordMat Tag.F4 (coxPow 10) = wordMat Tag.F4 (coxPow 10) * wordMat Tag.F4 r6a := by decide +kernel

theorem r6_comm_b : wordMat Tag.F4 r6b * wordMat Tag.F4 (coxPow 10) = wordMat Tag.F4 (coxPow 10) * wordMat Tag.F4 r6b := by decide +kernel

theorem r6_comm_c : wordMat Tag.F4 r6c * wordMat Tag.F4 (coxPow 10) = wordMat Tag.F4 (coxPow 10) * wordMat Tag.F4 r6c := by decide +kernel

theorem r6_comm_d : wordMat Tag.F4 r6d * wordMat Tag.F4 (coxPow 10) = wordMat Tag.F4 (coxPow 10) * wordMat Tag.F4 r6d := by decide +kernel

theorem r6_dc : wordMat Tag.F4 (cw (cw r6a r6b) (cw r6c r6d)) = (1 : ℤ) • wordMat Tag.F4 (coxPow 10) ^ 3 := by decide +kernel

end F4Data

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw
