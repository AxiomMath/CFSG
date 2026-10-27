module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.LitCompB
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.UHeredOfUgt
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCatalogueU

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.ComponentClassification
open CFSG.SignalizerFunctorTheorem (IsSectionOf)

theorem relativeUAt_of_uhered (hCU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    {X : Type} [Group X] [Finite X] (hX : Balance.UHered X) :
    KProperRelativeB.RelativeUAt CFSG.Blueprint.Catalog X := by
  intro hK hsimple hnonab hz
  by_contra hfail
  obtain ⟨htop, hXs, hXnab⟩ :=
    CatalogueU.kProper_unbalanced_U_failure_is_simple_of_catalogU hCU hK hsimple hnonab hz hfail
  obtain ⟨z, hz2, hzc⟩ := hz
  let e : GeneralizedFitting.subgroup X ≃* X :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  haveI := hXs
  refine hfail ?_
  rcases hX X (IsSectionOf.refl X) hXnab hK z hz2 hzc with
    ⟨t, n, p, f, hp, hp2, hadm, hmodel⟩ | ⟨n, hn7, hn3, ⟨θ⟩⟩
  · exact Or.inl ⟨t, n, p, f, hp, hp2, hadm, hmodel.of_mulEquiv e.symm⟩
  · exact Or.inr (Or.inl ⟨n, ⟨n / 2, by omega⟩, hn7, ⟨e.trans θ⟩, fun h => by omega⟩)

theorem relativeU_of_ugt (hCU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hUgt : Balance.UGTSimpleStatement) :
    KProperRelativeB.RelativeU CFSG.Blueprint.Catalog :=
  fun X _ _ => relativeUAt_of_uhered hCU (Balance.UHered.of_ugt hUgt X)

section FromUGT

theorem centralTwoBInclusion_of_uhered :
    ∀ (G : Type) [Group G] [Finite G], Balance.UHered G →
      CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → CentralTwoBInclusion.Property G :=
  centralTwoBInclusion_of_relativeUAt Balance.UHered (fun _ _ _ _ hY hXY => hY.of_section hXY)
    fun _ _ _ hX => relativeUAt_of_uhered FooteLit.catalogAlmostSimpleUnbalancedOutcome_holds hX

theorem bthm_of_uhered :
    ∀ (G : Type) [Group G] [Finite G], Balance.UHered G →
      CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
      CFSG.oddCore G = ⊥ → ∀ u : G, orderOf u = 2 → BTheoremAt u :=
  fun G _ _ hG hK hO u hu =>
    bthm_of_inclusionAt (centralTwoBInclusion_of_uhered G hG hK) hO u hu

theorem fs79Lemma15At_of_uhered (G : Type) [Group G] [Finite G] (hG : Balance.UHered G) :
    FS79Lemma15At G :=
  fun hK => fs79Lemma15At_of_inclusionAt (centralTwoBInclusion_of_uhered G hG hK) hK

end FromUGT

end CFSG.EvenSporadicStandard.Induction
