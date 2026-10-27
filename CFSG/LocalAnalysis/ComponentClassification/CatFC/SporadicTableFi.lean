module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableBasic
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatSporadic
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableDefs

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Sporadic.FischerOddCore
  (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven
    fi24primeOuterComponentsInput_holds fi23_mulAut_eq_conj)

section Fi22Row


theorem sporadic_rows_fi22 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Fi22) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .Fi22 (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .Fi22 (Nat.card (D ⧸ center D))) := by
  have h := SeitzReduction.UnitaryPilot.fi22_fixed_card_quotient hS hna e hσ hD
  exact ⟨fun hin => (h.1 hin).1, h.2⟩

end Fi22Row

section Fi23Row


theorem sporadic_rows_fi23 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Fi23) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .Fi23 (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .Fi23 (Nat.card (D ⧸ center D))) := by
  refine ⟨fun hin => inner_row_of_centralizer hS hna hσ hD hin
      (P := fun c => c = 64561751654400 ∨ c = 9196830720) (fun u hu B hB => ?_), fun hout => ?_⟩
  · exact SeitzReduction.UnitaryPilot.fi23_involution_component_card_quotient e u hu B hB
  · exact (false_of_not_mem_range (ComponentClassification.BMCase.inner_of_equiv e
      fi23_mulAut_eq_conj σ) hout).elim

end Fi23Row

section Fi24PrimeRow


theorem sporadic_rows_fi24 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Fi24Prime) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .Fi24Prime (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .Fi24Prime (Nat.card (D ⧸ center D))) := by
  refine ⟨fun hin => inner_row_of_centralizer hS hna hσ hD hin
      (P := fun c => c = 64561751654400) (fun u hu B hB => ?_), fun hout => ?_⟩
  · exact (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven
      e u hu B hB).1
  · obtain ⟨B, hB, hcard⟩ := SeitzReduction.OmegaPilot.exists_component_fixSub σ hD
    have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
    rw [← hcard]
    exact fi24primeOuterComponentsInput_holds S ⟨e⟩ σ hσ2 hout B hB

end Fi24PrimeRow

end CFSG.ComponentClassification.CatFC
