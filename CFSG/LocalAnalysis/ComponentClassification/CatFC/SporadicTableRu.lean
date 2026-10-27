module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableDefs
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporRu

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section RuRow


theorem sporadic_rows_ru {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Ru) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .Ru (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .Ru (Nat.card (D ⧸ center D))) := by
  refine ⟨fun hin => inner_row_of_centralizer hS hna hσ hD hin
      (P := fun c => ¬ 3 ∣ c) (fun u hu B hB => ?_), fun hout => ?_⟩
  · have h := ComponentClassification.RestrictedStd.Spor.compsSatisfy_centralizer_of_mulEquiv _
      ComponentClassification.RestrictedStd.Spor.isoInvariant_not_three_dvd
      ComponentClassification.RestrictedStd.Spor.ru_centralizerIn_comps
      (e.trans Sporadic.RuSchreier.ruEquivP) u hu B hB
    exact fun h3 => h (h3.trans (card_quotient_dvd_card _))
  · exact (false_of_not_mem_range (ComponentClassification.BMCase.inner_of_equiv
      (e.trans Sporadic.RuSchreier.ruEquivP) Sporadic.RuSchreier.mulAut_inner σ) hout).elim

end RuRow

end CFSG.ComponentClassification.CatFC
