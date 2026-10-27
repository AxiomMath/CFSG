module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreSporMain
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCoreHe

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.Blueprint

@[expose] def FooteCoreResidualLieInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K], SectionRank.IsKGroupCat K → ∀ a : K, orderOf a = 2 →
    ∀ Y : Subgroup K, IsPComponent 2 Y →
    (OddLieType (Y ⧸ Open.fusionZStar Y) ∨ EvenLieType (Y ⧸ Open.fusionZStar Y)) →
    (¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      LieModel (Y ⧸ Open.fusionZStar Y) .PSL 2 p f) →
    (¬ ∃ n : ℕ, Nonempty ((Y ⧸ Open.fusionZStar Y) ≃* alternatingGroup (Fin n))) →
    ¬ (OddOuterInner (Y ⧸ Open.fusionZStar Y) ∧ UBalanced (Y ⧸ Open.fusionZStar Y)) →
    ¬ Nonempty ((Y ⧸ Open.fusionZStar Y) ≃* NativeSporadic.He) →
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K

theorem footeCoreResidualInputNoHe_of_lie
    (hlie : FooteCoreResidualLieInput) (hON : ONanOuterCardLeTwo) :
    FooteCoreResidualInputNoHe := by
  intro K _ _ hK a ha Y hY hL2 halt hb hHe
  obtain ⟨hsimple, hna⟩ := zStarQuotient_simple hY
  have hcat : Catalog (Y ⧸ Open.fusionZStar Y) := hK Y (Open.fusionZStar Y) hsimple
  rcases (Milestones.ct_catalog_nonabelian_type_partition _ hna).mp hcat with
    ⟨n, -, ⟨e⟩⟩ | hodd | heven | hspor
  · exact absurd ⟨n, ⟨e⟩⟩ halt
  · exact hlie K hK a ha Y hY (Or.inl hodd) hL2 halt hb hHe
  · exact hlie K hK a ha Y hY (Or.inr heven) hL2 halt hb hHe
  · exact coreCondition_of_sporadicRep hON ha hY hspor hHe

end CFSG.ComponentClassification.Foote5
