module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineFourTwoStruct
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineFourListOfIdent
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35Holds
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.StrongThree
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsIdent
import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15

variable {G : Type} [Group G] [Finite G] {M Q H E : Subgroup G}

section Cert


private theorem nineFourListGroup_of_stronglyPEmbedded_five
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hX : CFSG.Open.IsKGroup X) (hO : CFSG.pPrimeCore p X = ⊥)
    (h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) {N K : Subgroup X} [K.Normal]
    (hKs : IsSimpleGroup ↥K) (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (hgen : CFSG.generalizedFitting X = K)
    (hA : 7 ≤ p → ¬ CFSG.AGLEmbedding.IsAltTwoP p ↥K)
    (hF : p = 5 → ¬ CFSG.AGLEmbedding.IsFi22 ↥K) :
    CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup p ↥K := by
  have h := CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.identification_of_isStronglyPEmbedded
    CFSG.LocalAnalysis.UniquenessCase.UCK.kFactSmallIdent_holds
    CFSG.LocalAnalysis.UniquenessCase.UCK.kFactOneLieIdent_holds
    CFSG.LocalAnalysis.UniquenessCase.UCK.stronglyEmbeddedCyclicOuter_holds
    hp hp5 hX hO h2 hN
  rw [hgen] at h
  exact CFSG.LocalAnalysis.RankThreeTheoremC.NineFour.nineFourListGroup_of_identification
    hp hp5 hKs hA hF h

private theorem nineFourListGroup_of_stronglyPEmbedded_three
    {X : Type} [Group X] [Finite X] (hX : CFSG.Open.IsKGroup X)
    (h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) {N K : Subgroup X} [K.Normal]
    (hKs : IsSimpleGroup ↥K) (hcent : Subgroup.centralizer (K : Set X) = ⊥)
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 N) :
    CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup 3 ↥K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKnab : ∃ a b : ↥K, a * b ≠ b * a := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hle : K ≤ Subgroup.centralizer (K : Set X) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (h ⟨y, hy⟩ ⟨x, hx⟩)
    rw [hcent] at hle
    exact (Subgroup.nontrivial_iff_ne_bot K).mp inferInstance (le_bot_iff.mp hle)
  obtain ⟨P, ⟨-, hPp, hPi⟩, hPN⟩ := hN.exists_isSylowOf_le
  let P' : Sylow 3 X := hPp.toSylow (by simpa [Subgroup.relIndex_top_right] using hPi)
  have hP' : (P' : Subgroup X) = P := IsPGroup.toSylow_coe hPp _
  have h2P : 2 ≤ CFSG.Open.pRank 3 (P' : Subgroup X) := by
    rw [(CFSG.SectionRank.pRank_sylow P').1]
    exact h2
  have hγ : CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.gammaCore 3 1 ⊤
      (P' : Subgroup X) < ⊤ := by
    have hle := CFSG.LocalAnalysis.UniquenessCase.UCK.gammaCore_le_of_isStronglyPEmbedded
      (p := 3) (A := ⊤) hN hPp hPN
    rw [← hP'] at hle
    exact hle.trans_lt (Ne.lt_top hN.1)
  have hplus := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
    X hX K inferInstance hKs hKnab hcent P' h2P hγ
  exact
    CFSG.LocalAnalysis.RankThreeTheoremC.NineFour.nineFourListGroup_three_of_gls3ConclusionPlus
      hplus

theorem nineFourListGroup_kStar_of_not
    {G : Type} [Group G] [Finite G] {M Q H E : Subgroup G}
    {p : ℕ} (s : NineSettingGen G M p Q H E 2) (hp : p ∈ sigmaM G M)
    (hL : ¬ pLayerIn p H ≤ M)
    (hΓ : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P (H ⊓ M) → rankThreeGamma 1 p P ≤ M)
    (hA : 7 ≤ p → ¬ CFSG.AGLEmbedding.IsAltTwoP p ↥(kStar p M H))
    (hF : p = 5 → ¬ CFSG.AGLEmbedding.IsFi22 ↥(kStar p M H)) :
    CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup p ↥(kStar p M H) := by
  haveI : Fact p.Prime := ⟨s.prime⟩
  obtain ⟨-, hkNormalSub, -, -, hKsimple, hKcent⟩ := nineFourTwo_structure s hp hL hΓ
  obtain ⟨hNstrong, hgenFit, -, h2, -⟩ := nineFourTwo_star s hp hL hΓ
  let X := H ⧸ primeComplementCore (G := H) p
  let K : Subgroup X := kStar p M H
  have hX : CFSG.Open.IsKGroup X :=
    (s.setting.cstar.kProper.isKGroup H s.ne_top).quotient (primeComplementCore (G := ↥H) p)
  have hO : CFSG.pPrimeCore p X = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥H) p
  have hKnorm : K.Normal :=
    hkNormalSub.map (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))
      (QuotientGroup.mk'_surjective _)
  haveI : K.Normal := hKnorm
  have h2' : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := h2
  by_cases h3 : p = 3
  · subst p
    exact nineFourListGroup_of_stronglyPEmbedded_three hX h2' hKsimple hKcent hNstrong
  · have hp5 : 5 ≤ p := by
      have h2p := s.prime.two_le
      have hne2 : p ≠ 2 := s.ne_two
      have hne3 : p ≠ 3 := h3
      obtain ⟨k, hk⟩ := s.prime.odd_of_ne_two hne2
      omega
    exact nineFourListGroup_of_stronglyPEmbedded_five s.prime hp5 hX hO h2' hKsimple hNstrong
      hgenFit hA hF

end Cert

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
