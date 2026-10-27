module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineSeventeenGeneric
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenRankOneDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineTwoOneEscape
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEscapeAt
import CFSG.LocalAnalysis.GLTheoremA.S8.Close
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineSeventeenCaseTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

theorem sq_dvd_card_component_of_escape (h31 : KFactThreeOne) (h75 : KFactSevenFive)
    (hR1 : KFactNineThreeListRankOne) (hSyl : KFactCaseTwoSylowAut) (hS : Setting G)
    (hKP : CFSG.Open.IsKProper G) {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G}
    (he : D1Escape p P M H₁ R₁) {B N : Subgroup G} (hB : IsAGLQ p M B) (hBN : B ≤ N)
    (hNtop : N ≠ ⊤) {L : Subgroup (N ⧸ primeComplementCore (G := N) p)} (hL : IsComponentOf L ⊤)
    (hLX : ¬ L ≤ d1X0 p M N) : p ^ 2 ∣ Nat.card L := by
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨i, hi, hiL⟩ := exists_nineThreeIndex_of_component h31 h75 hS hKP he hB hBN hNtop hL hLX
  by_cases h2 : 2 ≤ CFSG.Open.pRank p L
  · obtain ⟨E, hEL, -, hE⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank hp h2
    rw [← hE]
    exact Subgroup.card_dvd_of_le hEL
  · obtain ⟨T⟩ : Nonempty (Sylow p L) := inferInstance
    rw [← (hSyl p L (hR1 p _ L (Or.inl ⟨i, hi, hiL⟩) (by omega))).1 T]
    exact Subgroup.card_subgroup_dvd_card _

omit [Finite G] in
theorem not_le_bot_of_isComponentOf {X : Type} [Group X] {L : Subgroup X} (hL : IsComponentOf L ⊤) :
    ¬ L ≤ ⊥ := by
  intro hLb
  have hnt : Nontrivial (L ⧸ Subgroup.center L) := hL.2.2.2.toNontrivial
  haveI : Nontrivial L := (QuotientGroup.mk'_surjective (Subgroup.center L)).nontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : L)
  exact hx (Subtype.ext (Subgroup.mem_bot.mp (hLb x.2)))

theorem d1KBar_ne_bot_of_three_le (h31 : KFactThreeOne) (h75 : KFactSevenFive)
    (hR1 : KFactNineThreeListRankOne) (hSyl : KFactCaseTwoSylowAut) (h74 : AGL81SevenFourTwo)
    (hOutC : KFactOutCyclic) (hS : Setting G) (hKP : CFSG.Open.IsKProper G) {p : ℕ}
    {P : Sylow p G} {M H₁ R₁ : Subgroup G} (he : D1Escape p P M H₁ R₁) {B H N R : Subgroup G}
    (hB : IsAGLQ p M B) (hBH : B ≤ H) (hHtop : H ≠ ⊤)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (hLX : ¬ L ≤ d1X0 p M H) (hN : GLBIsMaxTwoLocal N) (hNM : ¬ N ≤ M)
    (hcov : AGLCovers p H N (d1KBar p M H)) (hRM : R ≤ M) (hR : CFSG.Quasithin.IsSylowIn p R N)
    (h3 : 3 ≤ CFSG.Open.pRank p R) : d1KBar p M N ≠ ⊥ := by
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  intro hKN
  obtain ⟨hLs, hLnab, -⟩ := isSimpleGroup_catalog_of_component h31 hKP he hB hBH hHtop hL hLX
  have hL2 := sq_dvd_card_component_of_escape h31 h75 hR1 hSyl hS hKP he hB hBH hHtop hL hLX
  have hLp : ∃ x : L, x ≠ 1 ∧ ∃ k : ℕ, x ^ p ^ k = 1 := by
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p ((dvd_pow_self p two_ne_zero).trans hL2)
    refine ⟨x, fun h => hp.one_lt.ne' ?_, 1, ?_⟩
    · rw [h, orderOf_one] at hx
      exact hx.symm
    · rw [pow_one]
      have h := pow_orderOf_eq_one x
      rwa [hx] at h
  obtain ⟨J, φ, hφ⟩ := exists_surjective_cover hLs hLp ((le_d1KBar hL hLX).trans hcov)
  obtain ⟨P', he'⟩ := exists_d1Escape_of_three_le he hN hNM hRM hR h3
  have hle : ∀ L' : Subgroup (N ⧸ primeComplementCore (G := N) p), IsComponentOf L' ⊤ →
      L' ≤ d1X0 p M N := fun L' hL' => by
    by_contra hL'X
    exact not_le_bot_of_isComponentOf hL' (hKN ▸ le_d1KBar hL' hL'X)
  have hc := he'.hasPrimeConstraint_of_forall_component_le h74 hOutC hKP hle
  obtain ⟨Tbar, -, hred⟩ := he'.reducedNongeneration
  exact false_of_layer_eq_bot_of_surjective hred (layer_eq_bot_of_exists_selfCentralizing hc) hLs
    hLnab φ hφ hL2

variable (G) in
@[expose] def AGL81NineSeventeenNotConstrained : Prop :=
  AGLGlobal G → ∀ (p : ℕ) (P : Sylow p G) (M H : Subgroup G), AGLMuAt p P M →
    GLBIsMaxTwoLocal H → ¬ H ≤ M →
    (∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M H) →
    ∀ B N : Subgroup G, IsAGLQ p M B → B ≤ H → GLBIsMaxTwoLocal N → ¬ N ≤ M → B ≤ N →
      AGLCovers p H N (d1KBar p M H) → d1KBar p M N ≠ ⊥

variable (G) in
@[expose] def AGL81NineSeventeenNotConstrainedTwo : Prop :=
  AGLGlobal G → ∀ (p : ℕ) (P : Sylow p G) (M H : Subgroup G), AGLMuAt p P M →
    GLBIsMaxTwoLocal H → ¬ H ≤ M →
    (∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M H) →
    ∀ B N : Subgroup G, IsAGLQ p M B → B ≤ H → GLBIsMaxTwoLocal N → ¬ N ≤ M → B ≤ N →
      AGLCovers p H N (d1KBar p M H) →
      (∀ R : Subgroup G, R ≤ M → CFSG.Quasithin.IsSylowIn p R N → CFSG.Open.pRank p R ≤ 2) →
      d1KBar p M N ≠ ⊥

theorem agl81NineSeventeenNotConstrained_of (h31 : KFactThreeOne) (h75 : KFactSevenFive)
    (hR1 : KFactNineThreeListRankOne) (hSyl : KFactCaseTwoSylowAut) (h74 : AGL81SevenFourTwo)
    (hOutC : KFactOutCyclic) (hS : Setting G) (hNC2 : AGL81NineSeventeenNotConstrainedTwo G) :
    AGL81NineSeventeenNotConstrained G := by
  intro hg p P M H hμ hH hHM hKex B N hB hBH hN hNM hBN hcov
  by_cases hr : ∀ R : Subgroup G, R ≤ M → CFSG.Quasithin.IsSylowIn p R N →
      CFSG.Open.pRank p R ≤ 2
  · exact hNC2 hg p P M H hμ hH hHM hKex B N hB hBH hN hNM hBN hcov hr
  push Not at hr
  obtain ⟨R, hRM, hR, h3⟩ := hr
  obtain ⟨H₁, R₁, he⟩ := hμ.escape
  obtain ⟨L, hL, hLX⟩ := hKex
  have hHtop : H ≠ ⊤ :=
    CFSG.LocalAnalysis.GLTheoremA.S8.isTwoLocal_ne_top hg.simple hg.nonab hH.1
  exact d1KBar_ne_bot_of_three_le h31 h75 hR1 hSyl h74 hOutC hS hg.kProper he hB hBH hHtop hL hLX
    hN hNM hcov hRM hR h3

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
