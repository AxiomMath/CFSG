module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.GH74.Generic.S1

variable {F : Type} [Field F] [Finite F]

theorem kl3_card_sl3 (hF3 : Nat.card F = 3) : Nat.card SL(3, F) = 5616 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := F) (n := 3) (by norm_num), hF3]
  rw [show Finset.Icc 2 3 = {2, 3} by rfl, Finset.prod_pair (by norm_num)]
  norm_num

theorem kl3_center_sl3 (hF3 : Nat.card F = 3) : Subgroup.center SL(3, F) = ⊥ := by
  have h := Nat.card_congr
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (n := Fin 3) (R := F) ⟨0, by norm_num⟩).toEquiv
  rw [CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd, hF3, Fintype.card_fin] at h
  have h1 : Nat.card (Subgroup.center SL(3, F)) = 1 := by
    rw [h]
    norm_num
  exact Subgroup.eq_bot_of_card_eq _ h1

omit [Finite F] in
theorem kl3_isPerfect_sl3 : Group.IsPerfect SL(3, F) :=
  CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)

theorem kl3_isSimple_sl3 (hF3 : Nat.card F = 3) : IsSimpleGroup SL(3, F) := by
  have h := (CFSG.LinearGroups.linear_projective_simple (K := F) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  exact ((QuotientGroup.quotientMulEquivOfEq (kl3_center_sl3 hF3)).trans
    QuotientGroup.quotientBot).isSimpleGroup_congr.1 h

theorem kl3_nonabelian_sl3 (hF3 : Nat.card F = 3) : ∃ a b : SL(3, F), a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have htop : center SL(3, F) = ⊤ :=
    eq_top_iff.2 fun x _ => Subgroup.mem_center_iff.2 fun g => hcon g x
  rw [kl3_center_sl3 hF3] at htop
  have hcard : Nat.card SL(3, F) = 1 := by
    rw [← Subgroup.card_top (G := SL(3, F)), ← htop, Subgroup.card_bot]
  rw [kl3_card_sl3 hF3] at hcard
  omega

end CFSG.GH74.Generic.S1
