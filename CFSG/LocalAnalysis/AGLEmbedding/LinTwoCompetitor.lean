module

public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.IIIaLists
public import CFSG.LocalAnalysis.AGLEmbedding.LemmaJStarOn
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoConfig
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedI
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedII
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedIII
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedO1
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutCard
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoReduced

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

namespace D1L2Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {n : ℕ} {P : Sylow p G}
  {M H R X : Subgroup G}

theorem not_le_of_nclIn_le (h : D1L2Config p n P M H R X) {H' : Subgroup G}
    (hJH' : nclIn H X ≤ H') : ¬ H' ≤ M := by
  intro hH'M
  obtain ⟨K, hKn, ⟨e⟩, -, hXK⟩ := h.socle
  obtain ⟨Rbar, -, hred⟩ := h.ext.reducedNongeneration
  have : K.Normal := hKn
  have hp : p.Prime := Fact.out
  obtain ⟨hTab, hTcard⟩ :=
    isElemAbelian_sylow_inf_of_psl2GF (by have := h.three_le; omega) e Rbar
  have hrank : 3 ≤ Open.pRank p ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) :=
    h.three_le.trans (le_csSup (pRank_bddAbove p hp _) ⟨_, le_rfl, hTab, hTcard⟩)
  refine not_le_of_weakCore_le hp Rbar hred.weakCore_le hred.ne_top hrank ?_
  rw [← h.map_nclIn_eq hKn ⟨e⟩ hXK]
  exact Subgroup.map_mono fun j hj => ⟨j.2, hH'M (hJH' hj)⟩

theorem card_dvd_of_isPGroup (h : D1L2Config p n P M H R X) {H' : Subgroup G}
    (h' : D1Escape p P M H' R) (S : Subgroup (H' ⧸ primeComplementCore (G := H') p))
    (hS : IsPGroup p S) : Nat.card S ∣ p ^ n * n := by
  obtain ⟨K, hKn, hKe, hC, -⟩ := h.socle
  obtain ⟨Rbar, hRbar, -⟩ := h.ext.reducedNongeneration
  obtain ⟨Rb, hRb, -⟩ := h'.reducedNongeneration
  have hp : p.Prime := Fact.out
  have hdvd : Nat.card (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ∣ p ^ n * n :=
    card_dvd_of_isPGroup_of_psl2GF kFactL2AutPCard h.ext.ne_two (by have := h.three_le; omega)
      hKn hKe hC _ Rbar.isPGroup'
  obtain ⟨T, hST⟩ := hS.exists_le_sylow
  have h1 : Nat.card (T : Subgroup (H' ⧸ primeComplementCore (G := H') p)) =
      Nat.card (Rb : Subgroup (H' ⧸ primeComplementCore (G := H') p)) := by
    rw [T.card_eq_multiplicity, Rb.card_eq_multiplicity]
  have h2 : Nat.card (Rb : Subgroup (H' ⧸ primeComplementCore (G := H') p)) = Nat.card R := by
    have hRp : IsPGroup p (R.subgroupOf H') := h'.isPGroup.comap_subtype
    rw [hRb, card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p) hRp,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h'.le_H).toEquiv]
  have h3 : Nat.card (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) = Nat.card R := by
    have hRp : IsPGroup p (R.subgroupOf H) := h.ext.isPGroup.comap_subtype
    rw [hRbar, card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p) hRp,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.ext.le_H).toEquiv]
  exact (Subgroup.card_dvd_of_le hST).trans (h1 ▸ h2 ▸ h3 ▸ hdvd)

theorem exists_jStarHyp (h : D1L2Config p n P M H R X) {H' : Subgroup G}
    (hext' : D1Extremal p P M H' R) (hJH' : nclIn H X ≤ H') :
    ∃ (Rb : Sylow p (H' ⧸ primeComplementCore (G := H') p))
      (φ : ((nclIn H X).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p))
        →* PSL2GF p n),
      (Rb : Subgroup (H' ⧸ primeComplementCore (G := H') p)) =
        (R.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) ∧
      JStarHyp p n Rb (((H' ⊓ M).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore p)))
        (((nclIn H X).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)))
        ((X.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p))) φ := by
  obtain ⟨Rb, hRb, hred⟩ := hext'.reducedNongeneration
  obtain ⟨φ, hs, hc, hk⟩ := h.exists_competitorHom hJH'
  refine ⟨Rb, φ, hRb, h.ext.ne_two, h.three_le, hred,
    (catalogSimpleSections_of_isKProper h.glob.kProper H' hext'.ne_top).quotient _, hs, hc, ?_,
    h.nclIn_map_eq hJH', ?_, ?_, h.card_dvd_of_isPGroup hext'.toD1Escape⟩
  · rw [hRb]
    exact Subgroup.map_mono (Subgroup.comap_mono h.le_R)
  · rw [hRb]
    exact h.map_le_normalizer_map hJH'
  · intro z hz
    rw [hRb] at hz
    exact h.faithful_of_mem_ker_iff hJH' hk z hz

theorem map_eq_inf_of_mulEquiv (h : D1L2Config p n P M H R X) {H' : Subgroup G}
    (hJH' : nclIn H X ≤ H') (Rb : Sylow p (H' ⧸ primeComplementCore (G := H') p))
    (hRb : (Rb : Subgroup (H' ⧸ primeComplementCore (G := H') p)) =
      (R.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)))
    (hJn : (((nclIn H X).subgroupOf H').map
      (QuotientGroup.mk' (primeComplementCore (G := H') p))).Normal)
    (hJe : Nonempty (((nclIn H X).subgroupOf H').map
      (QuotientGroup.mk' (primeComplementCore (G := H') p)) ≃* PSL2GF p n)) :
    (X.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) =
      (R.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) ⊓
        ((nclIn H X).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) := by
  obtain ⟨e⟩ := hJe
  have := hJn
  have hcard := (isElemAbelian_sylow_inf_of_psl2GF (by have := h.three_le; omega) e Rb).2
  rw [hRb] at hcard
  exact map_eq_inf_of_card_eq h.le_R h.le_H h.isPGroup hJH' (by rw [hcard, h.card_eq])

theorem competitor (hβ : KFactBeta) (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt)
    (hP1S : KFactP1ThreeSpor) (hEL : KFactJStarElimLie) (hEA : KFactJStarElimAlt)
    (hES : KFactJStarElimSpor) (h : D1L2Config p n P M H R X) {H' : Subgroup G}
    (hH' : GLBIsMaxTwoLocal H') (hJH' : nclIn H X ≤ H') (hRH' : R ≤ H') :
    D1L2Config p n P M H' R X ∧ nclIn H X ≤ nclIn H' X := by
  refine ⟨?_, h.nclIn_le_nclIn hJH'⟩
  have hext' : D1Extremal p P M H' R := h.ext.of_le hH' hRH' (h.not_le_of_nclIn_le hJH')
  obtain ⟨Rb, φ, hRb, hyp⟩ := h.exists_jStarHyp hext' hJH'
  obtain ⟨hJn, hJe, hJC⟩ := jStarConcl_of_cases jStarO1 (jStarII hβ) jStarI
    (jStarIII hP1L hP1A hP1S hEL hEA hES) hyp fun hcon => by
      obtain ⟨L, hL, -⟩ := isKProper_not_hasPrimeConstraint_catalog_component h.glob.kProper H'
        hext'.ne_top p Fact.out hcon
      exact ⟨L, hL⟩
  exact ⟨hext', h.glob, h.three_le, h.le_R,
    ⟨_, hJn, hJe, hJC, h.map_eq_inf_of_mulEquiv hJH' Rb hRb hJn hJe⟩, h.normal_sup⟩

end D1L2Config

@[expose] def StmtCompetitor : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {n : ℕ} {P : Sylow p G}
    {M R X : Subgroup G}, D1JCompetitorsOn (D1L2Config p n P M · R X) R X

theorem stmtCompetitor (hβ : KFactBeta) (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt)
    (hP1S : KFactP1ThreeSpor) (hEL : KFactJStarElimLie) (hEA : KFactJStarElimAlt)
    (hES : KFactJStarElimSpor) : StmtCompetitor :=
  fun _ h _ hH' hJH' hRH' => h.competitor hβ hP1L hP1A hP1S hEL hEA hES hH' hJH' hRH'

end CFSG.AGLEmbedding
