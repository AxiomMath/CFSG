module

public import CFSG.RankThree.SubgroupLists.SchurCommutant
public import CFSG.Open.StatedDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Matrix CFSG.RankThree.SubgroupLists

abbrev spFourJ (K : Type) [Field K] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks 0 1 (-1) 0

@[expose] def GLIrrQuasisimpleThreeDvd : Prop :=
  ∀ (r : ℕ) [Fact r.Prime], r ≠ 2 → ∀ d : ℕ, d ≤ 3 → ∀ Y : Subgroup (GL (Fin d) (ZMod r)),
    CFSG.IsQuasisimple Y → IsIrreducibleOn Y → 3 ∣ Nat.card Y

@[expose] def SpFourQuasisimpleThreeDvd : Prop :=
  ∀ (r : ℕ) [Fact r.Prime], r ≠ 2 → ∀ Y : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod r)),
    Y ≤ CFSG.Open.StatedSp 2 (ZMod r) → CFSG.IsQuasisimple Y → 3 ∣ Nat.card Y

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
