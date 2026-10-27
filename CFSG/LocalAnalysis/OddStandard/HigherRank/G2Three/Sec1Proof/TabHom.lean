module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open Subgroup

variable {Γ : Type} [Group Γ] {D : TabData} {elt : ℕ → Γ}

theorem card_S3S3 : Nat.card (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) = 36 := by
  rw [Nat.card_prod, Nat.card_perm, Nat.card_fin]
  rfl

theorem card_SL23 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) = 24 := by
  rw [Matrix.card_SL_field (n := 2) (𝔽 := ZMod 3), ZMod.card, Fin.prod_univ_two]
  norm_num

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
