module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCoreAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzCoverRank
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzDBridge

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def L34SuzSignalizerVanishing : Prop :=
  L34SignalizerVanishingAt fun X _ => Blueprint.NativeSporadic.IsSporadic X .Suz

@[expose] def L34SuzCoreOfSignalizer : Prop :=
  L34CoreOfSignalizerAt fun X _ => Blueprint.NativeSporadic.IsSporadic X .Suz

section Rank


theorem three_le_pRank_of_sporadic_suz_fusionZStar {G : Type} [Group G] [Finite G]
    {J : Subgroup G}
    (h : Blueprint.NativeSporadic.IsSporadic (J ⧸ Open.fusionZStar J) .Suz) :
    3 ≤ pRank 2 ↥J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eS⟩ := nonempty_quotient_center_equiv_fusionZStar ↥J
  obtain ⟨f⟩ := h
  have hS : Blueprint.NativeSporadic.IsSporadic
      ((↥J ⧸ pPrimeCore 2 ↥J) ⧸ center (↥J ⧸ pPrimeCore 2 ↥J)) .Suz := ⟨eS.trans f⟩
  have h1 := EvenSporadicStandard.Induction.suz_cover_rank
    EvenSporadicStandard.Induction.suzD_lieModel hS
  have hodd : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥J) := fun hd =>
    (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
      (even_iff_two_dvd.mpr hd)
  rwa [GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hodd] at h1

end Rank

section Certified


theorem l34SuzCoreStepMirror_of_signalizer
    (hS : SchreierFor Blueprint.Catalog) (hCI : GSLit.ClassicalInvolutionInput)
    (hGA : TBLit.GriessMultipliersAllModels) (h13 : Sol76T13.SolomonThm13Simple)
    (hS0 : L34SuzSignalizerVanishing) (hS1 : L34SuzCoreOfSignalizer) :
    L34SuzCoreStepMirror :=
  l34CoreStepMirrorAt_of_signalizer (fun _ _ h => Or.inl h)
    (fun _ _ _ _ e h => by
      obtain ⟨f⟩ := h
      exact ⟨e.symm.trans f⟩)
    (fun _ _ _ _ h => three_le_pRank_of_sporadic_suz_fusionZStar h) hS hCI hGA h13 hS0 hS1

end Certified

end CFSG.ComponentClassification.GrSLit.L34Sec5S
