module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27E6
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27DiagMain

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section


theorem twentySeven_dvd_fixedSubgroup_E6_unconditional {ℓ f : ℕ} [Fact ℓ.Prime]
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f)
    (α : MulAut (adjointGroup Tag.E6 K)) (hα3 : α ^ 3 = 1)
    (hα : α ∉ inner (adjointGroup Tag.E6 K)) : 27 ∣ Nat.card (fixedSubgroup α) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]; exact (pow_pos (Fact.out : ℓ.Prime).pos f).ne')
  refine twentySeven_dvd_fixedSubgroup_adjointE_of_diag .E6 (Or.inl rfl)
    twentySeven_dvd_card_adjointGroup_E6 hf K hK Nat.prime_three (by norm_num) α hα3 hα ?_
  intro g a hga
  exact e6DiagCase_unfolded K g a α (prime_dvd_of_diag_noninner .E6 (Or.inl rfl) K
    Nat.prime_three g a α hga hα3 hα).2 hga hα3 hα

theorem twentySeven_dvd_fixedSubgroup_E6 {ℓ f : ℕ} [Fact ℓ.Prime]
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f)
    (α : MulAut (adjointGroup Tag.E6 K)) (hα3 : α ^ 3 = 1)
    (hα : α ∉ inner (adjointGroup Tag.E6 K)) : 27 ∣ Nat.card (fixedSubgroup α) :=
  twentySeven_dvd_fixedSubgroup_E6_unconditional hf K hK α hα3 hα

end

end CFSG.HardMathSupport.Lang.E6Descent
