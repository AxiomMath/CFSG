module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.InnerOnK
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen
import CFSG.Models.PGLOrders

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.Assembly.RankThreeEven (projSL)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem HypCGen.toNineSettingGen {M : Subgroup G} {q : ℕ} {E H : Subgroup G}
    (h : HypCGen G M q E H) : NineSettingGen G M q E H E 2 where
  setting :=
    { cstar := h.cstar
      maxLocal := h.maxLocal
      sigma_nonempty := h.sigma_nonempty }
  mem_Q := h.mem_QSet
  mem_H := h.mem_HFam
  stdE := ⟨Or.inl rfl, le_rfl, h.elem, h.card, h.gamma⟩

theorem HypCGen.toNineCore {M : Subgroup G} {q : ℕ} {E H : Subgroup G}
    (h : HypCGen G M q E H) : NineCore G M q E H E 2 :=
  h.toNineSettingGen.toCore

@[expose] def KNormalCaseThreeAt (M : Subgroup G) : Prop :=
  ∀ E H : Subgroup G, HypCGen G M 3 E H → CaseThree M H →
    H ≤ Subgroup.normalizer (kSub 3 M H : Set G)

theorem kNormalAt_of_caseThree {M : Subgroup G} (hpre : PreambleTypes M)
    (h14 : ∀ H ∈ H2StarAll M, CaseThree M H) (h : KNormalCaseThreeAt M) : KNormalAt M := by
  intro q E H hdata
  have hq3 : q = 3 := eq_three_of_mem hpre hdata.mem_QSet hdata.mem
  subst q
  exact h E H hdata (h14 H ⟨3, E, hdata.mem_QSet, hdata.mem⟩)

theorem exists_le_pPrimeCore_card_map_quotient_eq_index (p : ℕ) {K H : Subgroup G}
    (hKH : K ≤ H) :
    ∃ N : Subgroup ↥K, N ≤ CFSG.pPrimeCore p ↥K ∧
      Nat.card ((K.subgroupOf H).map
        (QuotientGroup.mk' (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore
          (G := ↥H) p))) = N.index := by
  classical
  let O : Subgroup ↥H :=
    CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) p
  let incl : ↥K →* ↥H := Subgroup.inclusion hKH
  let f : ↥K →* ↥H ⧸ O := (QuotientGroup.mk' O).comp incl
  have hker : f.ker = O.comap incl := by
    ext x
    simp [f, QuotientGroup.eq_one_iff]
  have hker_card : Nat.card f.ker ∣ Nat.card O := by
    rw [hker]
    exact Subgroup.card_comap_dvd_of_injective O incl (Subgroup.inclusion_injective hKH)
  have hker_cop : Nat.Coprime p (Nat.card f.ker) :=
    (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore_coprime (G := ↥H) p).of_dvd_right
      hker_card
  have hle : f.ker ≤ CFSG.pPrimeCore p ↥K := by
    dsimp [CFSG.pPrimeCore]
    exact le_sSup ⟨MonoidHom.normal_ker f, hker_cop⟩
  have hrange : f.range = (K.subgroupOf H).map (QuotientGroup.mk' O) := by
    dsimp [f]
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  refine ⟨f.ker, hle, ?_⟩
  rw [← hrange, Subgroup.index_eq_card]
  exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv).symm

theorem card_pPrimeCore_quotient_dvd_card_map_quotient (p : ℕ) {K H : Subgroup G}
    (hKH : K ≤ H) :
    Nat.card (↥K ⧸ CFSG.pPrimeCore p ↥K) ∣
      Nat.card ((K.subgroupOf H).map
        (QuotientGroup.mk' (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore
          (G := ↥H) p))) := by
  obtain ⟨N, hNle, hNindex⟩ := exists_le_pPrimeCore_card_map_quotient_eq_index p hKH
  rw [hNindex, ← Subgroup.index_eq_card]
  exact Subgroup.index_dvd_of_le hNle

theorem coprime_card_map_quotient_div_card_pPrimeCore_quotient (p : ℕ) [Fact p.Prime]
    {K H : Subgroup G} (hKH : K ≤ H) :
    Nat.Coprime p
      (Nat.card ((K.subgroupOf H).map
          (QuotientGroup.mk' (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore
            (G := ↥H) p))) /
        Nat.card (↥K ⧸ CFSG.pPrimeCore p ↥K)) := by
  obtain ⟨N, hNle, hNindex⟩ := exists_le_pPrimeCore_card_map_quotient_eq_index p hKH
  have hcop_core : Nat.Coprime p (Nat.card (CFSG.pPrimeCore p ↥K)) :=
    CFSG.pPrimeCore_coprime_card
  have hrel : N.index / (CFSG.pPrimeCore p ↥K).index =
      N.relIndex (CFSG.pPrimeCore p ↥K) := by
    rw [← Subgroup.relIndex_mul_index hNle]
    exact Nat.mul_div_left _ (by
      rw [Subgroup.index_eq_card]
      exact Nat.card_pos)
  rw [hNindex, ← Subgroup.index_eq_card, hrel]
  exact hcop_core.of_dvd_right (Subgroup.relIndex_dvd_card N (CFSG.pPrimeCore p ↥K))

theorem card_threeStar_dvd_card_kStar {M H : Subgroup G} :
    Nat.card (threeStar (kSub 3 M H)) ∣ Nat.card (kStar 3 M H) := by
  simpa [threeStar, kStar] using
    card_pPrimeCore_quotient_dvd_card_map_quotient (p := 3) (K := kSub 3 M H) (H := H)
      (kSub_le 3 M H)

theorem coprime_card_kStar_div_card_threeStar {M H : Subgroup G} :
    Nat.Coprime 3
      (Nat.card (kStar 3 M H) / Nat.card (threeStar (kSub 3 M H))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  simpa [threeStar, kStar] using
    coprime_card_map_quotient_div_card_pPrimeCore_quotient (p := 3) (K := kSub 3 M H) (H := H)
      (kSub_le 3 M H)

theorem card_threeStar_of_caseThree {M H : Subgroup G} (hC3 : CaseThree M H) :
    Nat.card (threeStar (kSub 3 M H)) = 20160 := by
  obtain ⟨e⟩ := HypCGen.nonempty_mulEquiv_threeStar hC3
  rw [Nat.card_congr e.toEquiv, CFSG.PGLModel.card_projSL_three_four]

private theorem false_of_shape_card {m n : ℕ} (hn : n = 20160 ∨ n = 19958400)
    (hm : m ∣ 504 ∨ m = 1080 ∨ m = 60480) (hcop : Nat.Coprime 3 (m / n)) : False := by
  rcases hn with rfl | rfl
  · rcases hm with hm | rfl | rfl
    · have hmle : m ≤ 504 := Nat.le_of_dvd (by norm_num) hm
      rw [Nat.div_eq_of_lt (by omega : m < 20160)] at hcop
      norm_num at hcop
    · norm_num at hcop
    · norm_num at hcop
  · rcases hm with hm | rfl | rfl
    · have hmle : m ≤ 504 := Nat.le_of_dvd (by norm_num) hm
      rw [Nat.div_eq_of_lt (by omega : m < 19958400)] at hcop
      norm_num at hcop
    · norm_num at hcop
    · norm_num at hcop

theorem le_normalizer_kSub_of_nineTenConclusion {M E H : Subgroup G}
    (hconcl : NineTenConclusion G M E H E 3) (hLp : ¬ pLayerIn 3 H ≤ M)
    (hcard : Nat.card (threeStar (kSub 3 M H)) = 20160 ∨
      Nat.card (threeStar (kSub 3 M H)) = 19958400) :
    H ≤ Subgroup.normalizer (kSub 3 M H : Set G) := by
  rcases hconcl.1 hLp with ⟨-, -, hnormal⟩ | ⟨-, hshape, -⟩
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer (kSub_le 3 M H)).mp hnormal
  · exfalso
    have hcop := coprime_card_kStar_div_card_threeStar (M := M) (H := H)
    have hcardSL2 : Nat.card
        (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3)) = 504 := by
      have hK8 : Nat.card (GaloisField 2 3) = 8 := by
        rw [GaloisField.card 2 3 (by norm_num)]
        norm_num
      have : Fintype (GaloisField 2 3) := Fintype.ofFinite _
      rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, hK8]
      decide
    have hcardA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have hcardSL3 : Nat.card
        (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) = 60480 := by
      have hK : Nat.card (GaloisField 2 2) = 4 := by
        rw [GaloisField.card 2 2 (by norm_num)]
        norm_num
      have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
      rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, hK]
      decide
    have hm : Nat.card (kStar 3 M H) ∣ 504 ∨ Nat.card (kStar 3 M H) = 1080 ∨
        Nat.card (kStar 3 M H) = 60480 := by
      rcases hshape with hL2 | hA6Z3 | hSL3
      · obtain ⟨e⟩ := hL2
        left
        have hPSLdvd : Nat.card
            (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3)) ∣ 504 := by
          simpa [hcardSL2] using
            Subgroup.card_quotient_dvd_card
              (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3)))
        rwa [Nat.card_congr e.toEquiv]
      · obtain ⟨N, hN, hbody⟩ := hA6Z3
        obtain ⟨hNcard, hrest⟩ := hbody
        obtain ⟨hA, -⟩ := hrest
        obtain ⟨e⟩ := hA
        right; left
        have hquot : Nat.card (↥(kStar 3 M H) ⧸ N) = 360 := by
          rw [Nat.card_congr e.toEquiv, hcardA6]
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (s := N), hquot, hNcard]
      · obtain ⟨e⟩ := hSL3
        right; right
        rwa [Nat.card_congr e.toEquiv]
    exact false_of_shape_card hcard hm hcop

theorem kNormalCaseThreeAt_of {M : Subgroup G} (h10 : NineTenGen) (hL : PLayerNotLeAt M) :
    KNormalCaseThreeAt M := by
  intro E H hdata hC3
  have hsigma : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M := by
    simpa [CFSG.LocalAnalysis.AGL81TheoremCD.sigmaSet,
      CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using hdata.not_mem_sigmaSet
  have hconcl : NineTenConclusion G M E H E 3 :=
    h10 G M E H E 3 hdata.toNineSettingGen hdata.mem_H2Fam hsigma
  exact le_normalizer_kSub_of_nineTenConclusion hconcl (hL 3 E H hdata)
    (Or.inl (card_threeStar_of_caseThree hC3))

theorem agl81FourteenFifteen_of_nineTen
    (hF : KFactL34FixedPointsGen) (h10 : NineTenGen)
    (h : ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
      CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
        PreambleTypes M ∧ ChoiceExists M ∧ CaseOneFalse M ∧ CaseTwoFalse M ∧
          FourteenFifteenNormAt M ∧ PLayerNotLeAt M ∧ NineNineOneAt M) :
    AGL81FourteenFifteen := by
  refine agl81FourteenFifteen_of_kFact hF ?_
  intro G _ _ hC M hM hσ
  obtain ⟨hpre, hch, h1, h2, hN, hL, hU⟩ := h G hC M hM hσ
  have h14 : ∀ H ∈ H2StarAll M, CaseThree M H := caseThree_of_cases hpre hch h1 h2
  have hK : KNormalAt M :=
    kNormalAt_of_caseThree hpre h14 (kNormalCaseThreeAt_of h10 hL)
  exact ⟨hpre, hch, h1, h2, hN, hK, hL, hU⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
