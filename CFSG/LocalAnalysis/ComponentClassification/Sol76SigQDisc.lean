module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigSplit
public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigFourConn
public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigGammaLift
public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigGammaCore
public import CFSG.LocalAnalysis.ComponentClassification.Sol76R12Sp4

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

@[expose] def SolomonQTwoDisconnectedSylowFor : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K ∈ kStarComponents N, ∀ K' ∈ kStarComponents N, K ≠ K' →
      IsTwoDisconnected ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K') →
      3 ≤ CFSG.Open.pRank 2 K →
      (∃ (S' : Sylow 2 ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K'))
          (E F : Subgroup ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K')),
          IsKleinFour E ∧ E ≤ S' ∧ IsKleinFour F ∧ F ≤ S' ∧
            ¬ Relation.ReflTransGen
              (CommFourAdj ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K')) E F) →
      IsSolomonI (coreQuot K)

section Certified

theorem solomonQTwoDisconnectedFor_of_sylow (hBig : QuasisimpleBigCenterRankThree)
    (hS : SolomonQTwoDisconnectedSylowFor) : SolomonQTwoDisconnectedFor := by
  intro G _ _ hG N hN hr K hK K' hK' hne hdisc h3
  by_contra hI
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pPrimeCore 2 (coreQuot K) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥K) 2
  have h3' : 3 ≤ CFSG.Open.twoRank (coreQuot K) := by
    show 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (↥K ⧸ pPrimeCore 2 ↥K))
    rw [← SectionRank.pRank_eq_open_pRank_top, FooteLit.pRank_quotient_pPrimeCore, pRank_coe_eq]
    exact h3
  have hΓK : ∀ Tb : Sylow 2 (↥K ⧸ pPrimeCore 2 ↥K),
      CFSG.Open.properTwoGenCoreGamma (Tb : Subgroup (↥K ⧸ pPrimeCore 2 ↥K)) 2 = ⊤ := fun Tb =>
    gamma_eq_top_of_not_isSolomonI hBig (isQuasisimple_quotient_of_isPComponent hK.1.1 hK.1.2) hO
      (catalog_coreQuotient_of_mem_solomonKStar (kStarKProper_of_simpleAmbient hG) hK.1 hK.2)
      (R12.isPGroup_center_of_pPrimeCore_eq_bot hO) h3' hI Tb
  obtain ⟨S', hS'⟩ := exists_sylow_gamma_eq_top_of_mem_kStarComponents hr hK hK' hne h3 hΓK
  obtain ⟨E, F, hE, hES, hF, hFS, hEF⟩ := exists_not_reflTransGen_of_isTwoDisconnected S' hS' hdisc
  exact hI (hS G hG N hN hr K hK K' hK' hne hdisc h3 ⟨S', E, F, hE, hES, hF, hFS, hEF⟩)

end Certified

end CFSG.ComponentClassification.Sol76.Sig
