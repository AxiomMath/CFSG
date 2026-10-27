module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSec4

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit

variable {G : Type} [Group G] [Finite G]

theorem eq_of_isTwoComponentAt_of_pRank_le_two (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) {L : Subgroup G}
    (hLfam : FooteFamilyType L) (hrank2 : ∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2)
    (hrankC : ∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥(coreActionKernel A) ≤ 2) {a : G}
    {K M : Subgroup G} (hK : IsTwoComponentAt a K) (hM : IsTwoComponentAt a M)
    (hKF : K ∈ footeFamilyOf L) (hMF : M ∈ footeFamilyOf L) : K = M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have ha := hK.1
  obtain ⟨-, ⟨eML⟩⟩ := id hMF
  have hMfam : FooteFamilyType M := footeFamilyType_of_equiv eML hLfam
  have hMq := isQuasisimple_quotient_of_isPComponent hM.2.1 hM.2.2
  have hZM : center (M ⧸ pPrimeCore 2 M) = ⊥ := by
    by_contra hZ
    have h1 := pRank_le_one_of_center_ne_bot hMq hMfam
      (card_center_le_two_of_footeFamilyType hGA hGC hSA G M ⟨a, hM⟩ hMfam) hZ
    rw [hrank2 M hMF] at h1
    omega
  have haM : a ∉ M := fun haM => center_ne_bot_of_mem_coreActionKernel haM ha
    (GSLit.mem_coreActionKernel_of_le_centralizer hM.2.1) hZM
  have hMK : M ≤ coreActionKernel K :=
    GSThmB.B5a.le_coreActionKernel_of_ne hK.2.1 hM.2.1 hK.2.2 hM.2.2 hne
  have haK : a ∈ coreActionKernel K := GSLit.mem_coreActionKernel_of_le_centralizer hK.2.1
  have hrM : CFSG.Open.pRank 2 M = 2 := by
    have h := hrank2 M hMF
    rwa [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at h
  obtain ⟨E, hEM, hE, hEcard⟩ := SectionRank.exists_pRank one_lt_two M
  rw [hrM] at hEcard
  have ha2 : a ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have h3 := succ_le_open_pRank_of_commute Nat.prime_two hE hEcard
    (fun x hx => mem_centralizer_singleton_iff.mp (hM.2.1 (hEM hx))) ha2 (fun h => haM (hEM h))
    (hEM.trans hMK) haK
  have h4 := hrankC K hKF
  rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at h4
  omega

theorem footeSec4_of_rank_le_two (hLB : FooteLBalanceInput)
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) (hOut : FooteL2OutAbelian)
    (hAb : FooteL2AbelianCore) (h9 : FooteL2NineOddInner) (hRk : FooteL2RankThree)
    (hSolv : FooteL2InvolutionSolvable) {t : G} {L : Subgroup G}
    (hce : FooteCounterexample G t L) (hsimple : IsSimpleGroup G)
    (hrank2 : ∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2)
    (hrankC : ∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥(coreActionKernel A) ≤ 2) :
    FooteSec4 G L where
  hLB := hLB
  hCI := hCI
  hGA := hGA
  hGC := hGC
  hSA := hSA
  hOut := hOut
  hAb := hAb
  h9 := h9
  hRk := hRk
  hSolv := hSolv
  simple := hsimple
  ce := ⟨t, hce⟩
  huniq := fun _ _ _ hK hM hKF hMF =>
    eq_of_isTwoComponentAt_of_pRank_le_two hGA hGC hSA hce.1.2.2.2.2.1 hrank2 hrankC hK hM hKF
      hMF
  hrank2 := hrank2

end CFSG.ComponentClassification.Foote5
