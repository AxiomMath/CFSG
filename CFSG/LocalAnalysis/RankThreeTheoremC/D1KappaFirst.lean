module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KExtremal
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KappaTop
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineShared
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedPhase3Main

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111 CFSG.AGLEmbeddingD2
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G]

theorem D1KExtremal.kappa_le_of_escape {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1KExtremal p P M H R) {P' : Sylow p G} {M' N R' : Subgroup G}
    (he : D1Escape p P' M' N R') : d1Kappa p M' N ≤ d1Kappa p M H :=
  h.kappa_max P' M' N R' he

theorem D1KExtremal.kappaIH {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1KExtremal p P M H R) : D1KappaIH p M H :=
  fun P' M' N R' hext hlt => (h.kappa_max P' M' N R' hext.toD1Escape).not_gt hlt

theorem kExtremal_of_extremal {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1Extremal p P M H R)
    (hk : ∀ (P' : Sylow p G) (M' N R' : Subgroup G), D1Escape p P' M' N R' →
      d1Kappa p M' N ≤ d1Kappa p M H) : D1KExtremal p P M H R :=
  { toD1Escape := h.toD1Escape
    kappa_max := hk
    extremalK := fun N hN hNM h3 _ => h.extremal N hN.1 hNM h3
    extremalK3 := fun N hN hNM h3 _ => h.extremal3 N hN.1 hNM h3 }

theorem kappa_le_of_covers (h9 : AGL81NineCompetitor G) (hg : AGLGlobal G) {p : ℕ}
    {P : Sylow p G} {M H R : Subgroup G} (he : D1Escape p P M H R)
    (hK : ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M H) {B N : Subgroup G} (hB : IsAGLQ p M B) (hBH : B ≤ H)
    (hN : GLBIsMaxTwoLocal N) (hNM : ¬ N ≤ M) (hBN : B ≤ N)
    (hcov : AGLCovers p H N (d1KBar p M H)) : d1Kappa p M H ≤ d1Kappa p M N :=
  (h9 hg p P M H R he hK B N hB hBH hN hNM hBN hcov).kappa_le

theorem D1KExtremal.le_of_covers (h9 : AGL81NineCompetitor G) (hg : AGLGlobal G) {p : ℕ}
    {P : Sylow p G} {M H R : Subgroup G} (h : D1KExtremal p P M H R)
    (hK : ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M H) {B H' X : Subgroup G} (hB : IsAGLQ p M B) (hBH : B ≤ H)
    (hH' : IsTwoLocal H') (hBH' : B ≤ H') (hcov : AGLCovers p H H' (d1KBar p M H))
    (hXM : X ≤ M) (hX : IsPGroup p X) (hX3 : 3 ≤ Open.pRank p X) (hXR : Nat.card R < Nat.card X)
    (hXH' : X ≤ H') : H' ≤ M := by
  obtain ⟨N, hH'N, hN⟩ := exists_maximal_twoLocal hH'
  by_cases hNM : N ≤ M
  · exact hH'N.trans hNM
  have hcovN : AGLCovers p H N (d1KBar p M H) := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := hcov hx
    have hy' : (y : G) ∈ H ⊓ H' := Subgroup.mem_subgroupOf.mp hy
    exact ⟨y, Subgroup.mem_subgroupOf.mpr ⟨hy'.1, hH'N hy'.2⟩, rfl⟩
  have hk := kappa_le_of_covers h9 hg h.toD1Escape hK hB hBH hN hNM (hBH'.trans hH'N) hcovN
  exact h.toOn.le_of_card_lt hXM hX hX3 hXR hH' hXH' ⟨N, hN, hH'N, hk⟩

variable (G) in
@[expose] def D1RankTwoTop : Prop :=
  AGLGlobal G → ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G), D1KExtremal p P M H R →
    ¬ HasPrimeConstraint (G := H) p →
    ∀ N Q : Subgroup G, GLBIsMaxTwoLocal N → ¬ N ≤ M → IsAGLQ p M Q → Q ≤ N →
      (∀ V : Subgroup G, V ≤ N → IsPGroup p V → Q ≤ V → V = Q) → Open.pRank p Q ≤ 2 →
      d1Kappa p M H < d1Kappa p M N →
      (∀ N' Q' : Subgroup G, GLBIsMaxTwoLocal N' → ¬ N' ≤ M → IsAGLQ p M Q' → Q' ≤ N' →
        d1Kappa p M N' ≤ d1Kappa p M N) → False

theorem normalizer_le_of_isAGLQ_of_escape {p : ℕ} {P : Sylow p G} {M H R U : Subgroup G}
    (he : D1Escape p P M H R) (hU : IsAGLQ p M U) : Subgroup.normalizer (U : Set G) ≤ M := by
  obtain ⟨K, R', hx⟩ := he.exists_extremal
  exact normalizer_le_of_isAGLQ hx hU

theorem D1KExtremal.kappa_le_of_rankTwoTop (hT : D1RankTwoTop G) (hg : AGLGlobal G) {p : ℕ}
    {P : Sylow p G} {M H R : Subgroup G} (h : D1KExtremal p P M H R)
    (hcon : ¬ HasPrimeConstraint (G := H) p) {N B : Subgroup G} (hN : GLBIsMaxTwoLocal N)
    (hNM : ¬ N ≤ M) (hB : IsAGLQ p M B) (hBN : B ≤ N) : d1Kappa p M N ≤ d1Kappa p M H := by
  classical
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  by_contra hlt
  push Not at hlt
  let S : Set (Subgroup G × Subgroup G) :=
    {a | GLBIsMaxTwoLocal a.1 ∧ ¬ a.1 ≤ M ∧ IsAGLQ p M a.2 ∧ a.2 ≤ a.1}
  obtain ⟨⟨N₀, B₀⟩, ⟨hN₀, hN₀M, hB₀, hB₀N⟩, hmax⟩ :=
    S.exists_max_image (fun a => d1Kappa p M a.1) S.toFinite ⟨(N, B), hN, hNM, hB, hBN⟩
  have hmax' : ∀ N' Q' : Subgroup G, GLBIsMaxTwoLocal N' → ¬ N' ≤ M → IsAGLQ p M Q' →
      Q' ≤ N' → d1Kappa p M N' ≤ d1Kappa p M N₀ :=
    fun N' Q' h1 h2 h3 h4 => hmax (N', Q') ⟨h1, h2, h3, h4⟩
  have hk₀ : d1Kappa p M H < d1Kappa p M N₀ := hlt.trans_le (hmax' N B hN hNM hB hBN)
  obtain ⟨Q₀, hBQ, hQN, hQM, hQ, hQmax⟩ := exists_maxPSubgroup_of_normalizer_le hB₀.2.1 hB₀N
    hB₀.1 fun U hBU hUM hU => normalizer_le_of_isAGLQ_of_escape h.toD1Escape (isAGLQ_of_le hB₀ hBU hUM hU)
  by_cases h3 : 3 ≤ Open.pRank p (N₀ ⊓ M)
  · obtain ⟨T, hTM, hTrank, -⟩ := intersecting_local_has_contained_sylow p hp P h.sylow_le
      h.weakCore_le h3
    obtain ⟨P', he'⟩ := exists_d1Escape_of_sylow h.toD1Escape hN₀ hN₀M T hTM hTrank
    exact (h.kappa_max _ _ _ _ he').not_gt hk₀
  · push Not at h3
    have hQ2 : Open.pRank p Q₀ ≤ 2 := by
      have hle : Open.pRank p Q₀ ≤ Open.pRank p (N₀ ⊓ M) :=
        CFSG.SectionRank.pRank_mono hp.one_lt (le_inf hQN hQM)
      omega
    exact hT hg p P M H R h hcon N₀ Q₀ hN₀ hN₀M (isAGLQ_of_le hB₀ hBQ hQM hQ) hQN hQmax hQ2 hk₀
      fun N' Q' h1 h2 h3 h4 => hmax' N' Q' h1 h2 h3 h4

structure D1ComponentConfigK3 (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)) : Prop where
  glob : Setting G
  loc : D1Local3 p P M
  kext : D1KExtremal p P M H R
  notCon : ¬ HasPrimeConstraint (G := H) p
  ind : ∀ q ∈ rankThreeSigmaA G, q < p → D1At3 G q
  rbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))
  red : ReducedNongeneration p (H ⧸ primeComplementCore (G := H) p) Rbar
    (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
  catalog : CatalogSimpleSections (H ⧸ primeComplementCore (G := H) p)

theorem exists_componentConfigK3 (hS : Setting G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M H R : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (hext : D1KExtremal p P M H R) (hcon : ¬ HasPrimeConstraint (G := H) p)
    (hind : ∀ q ∈ rankThreeSigmaA G, q < p → D1At3 G q) :
    ∃ Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p),
      D1ComponentConfigK3 p P M H R Rbar := by
  obtain ⟨Rbar, hRbar, hred, hX, -⟩ :=
    hext.toD1Escape.exists_reducedNongeneration_of_not_hasPrimeConstraint hS.kProper hcon
  exact ⟨Rbar, hS, ⟨hp, hM.1, hM.2⟩, hext, hcon, hind, hRbar, hred, hX⟩

theorem D1ComponentConfigK3.toConfig3 {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)} (h : D1ComponentConfigK3 p P M H R Rbar)
    (hext : D1Extremal p P M H R) : D1ComponentConfig3 p P M H R Rbar :=
  ⟨h.glob, h.loc, hext, h.notCon, h.ind, h.rbar, h.red, h.catalog⟩

theorem D1ComponentConfigK3.pRank_rbar_eq_three {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)} (h : D1ComponentConfigK3 p P M H R Rbar) :
    Open.pRank p (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) = 3 := by
  have hp := h.kext.prime
  have h3 := h.red.three_le_pRank
  have hP3 : Open.pRank p (P : Subgroup G) = 3 :=
    (sylow_le_of_isCoreMaxLocal h.glob h.loc.sigma h.loc.isCoreMaxLocal).2
  have hle : Open.pRank p (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤ 3 := by
    rw [h.rbar, pRank_map_mk_eq_pRank_map_subtype hp _ (primeComplementCore_coprime p),
      Subgroup.map_subgroupOf_eq_of_le h.kext.le_H]
    exact (PreuniquenessRankFour.Helpers.pRank_mono p hp h.kext.le_P).trans hP3.le
  omega

@[expose] def D1CaseOneSmall3KF (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfigK3 p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      Subgroup.center K = ⊥ →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∃ z ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)), z ∉ K ∧ orderOf z = p ∧
        z ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))) →
      Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 →
      Open.pRank p (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) = 3 → False

@[expose] def D1CaseTwo3KF (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfigK3 p P M H R Rbar →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
        Subgroup (H ⧸ primeComplementCore (G := H) p))) → False

@[expose] def D1CaseThree3KF (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfigK3 p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) → False

@[expose] def D1ComponentCaseKF3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ p ∈ rankThreeSigmaA G, (∀ q ∈ rankThreeSigmaA G, q < p → D1At3 G q) →
    ∀ (P : Sylow p G) (M : Subgroup G), IsCoreMaxLocal p P M → ∀ H R : Subgroup G,
      D1KExtremal p P M H R → ¬ HasPrimeConstraint (G := H) p → False

theorem d1ComponentCaseKF3_of_cases (hK3 : KFactsA3 G) (h1s : D1CaseOneSmall3KF G)
    (h2 : D1CaseTwo3KF G) (h3 : D1CaseThree3KF G) : D1ComponentCaseKF3 G := by
  intro hS p hp hind P M hM H R hext hcon
  obtain ⟨Rbar, hcfg⟩ := exists_componentConfigK3 hS hp hM hext hcon hind
  have hred := hcfg.red
  by_cases hall : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
        Subgroup (H ⧸ primeComplementCore (G := H) p))
  · exact h2 p P M H R Rbar hcfg hall
  push Not at hall
  obtain ⟨K, hK, hnc⟩ := hall
  rcases hred.rankOne_or_center hK hnc with ⟨z, hzR, hzK, hzp, hzc, hN, hKX₀, -, hZ⟩ | hcent
  · have hAut := pRank_mulAut_le_two3 hred hcfg.pRank_rbar_eq_three.le hcfg.catalog hK3.beta hK hZ
      hzR hzp hzK hzc hN hKX₀
    exact h1s p P M H R Rbar hcfg K hK hZ hnc ⟨z, hzR, hzK, hzp, hzc⟩ hAut
      (hred.pRank_eq_three_of_pRank_mulAut_le_two hK hKX₀ hAut)
  · exact h3 p P M H R Rbar hcfg K hK (fun L hL => hred.eq_of_forall_mem_center hK hL hcent)
      hnc hcent

theorem componentAt_of_KF (hK : D1ComponentCaseKF3 G) (hS : Setting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) (hind : ∀ q ∈ rankThreeSigmaA G, q < p → D1At3 G q) :
    ∀ (P : Sylow p G) (M : Subgroup G), IsCoreMaxLocal p P M → ∀ H R : Subgroup G,
      D1Extremal p P M H R → ¬ HasPrimeConstraint (G := H) p → False := by
  have : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  intro P M hM H R hext hc
  obtain ⟨P₀, M₀, H₀, R₀, h₀⟩ := exists_d1KExtremal_of_escape hext.toD1Escape
  by_cases h1 : d1Kappa p M₀ H₀ = 1
  · refine hK hS p hp hind P M hM H R (kExtremal_of_extremal hext fun P' M' N R' he => ?_) hc
    exact (h₀.kappa_max P' M' N R' he).trans (h1.le.trans (one_le_d1Kappa p M H))
  · refine hK hS p hp hind P₀ M₀ ⟨h₀.maxTwoLocal_M, h₀.weakCore_le⟩ H₀ R₀ h₀ ?_
    intro hc₀
    exact h1 (d1Kappa_eq_one_of_hasPrimeConstraint hc₀)

theorem d1ExtremalCase3_of_cases_kFirst
    (hcon : D1ComponentCaseInd3 G → D1ConstrainedCaseInd3 G) (hK : D1ComponentCaseKF3 G) :
    D1ExtremalCase3 G := by
  refine d1ExtremalCase3_iff_forall_extremalAt3.mpr fun hS => ?_
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp P M hM H R hext
    have hind : ∀ q ∈ rankThreeSigmaA G, q < p → D1At3 G q := fun q hq hqp =>
      d1At3_of_extremalAt3 hq (ih q hqp hq)
    have hcompP := componentAt_of_KF hK hS hp hind
    by_cases hc : HasPrimeConstraint (G := H) p
    · refine hcon ?_ hS p hp hind P M hM H R hext hc
      intro _ q hq hindq Q M' hM' H' R' hext' hc'
      rcases lt_trichotomy q p with hqp | rfl | hpq
      · exact false_of_d1At3_of_extremal (hind q hq hqp) hM' hext'
      · exact hcompP Q M' hM' H' R' hext' hc'
      · exact false_of_d1At3_of_extremal (hindq p hp hpq) hM hext
    · exact hcompP P M hM H R hext hc

theorem theoremD1_of_phase3_residuesKF (hS : Setting G) (hK3 : KFactsA3 G)
    (hnone : D1ComponentAlphaNone3 G) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (h1s : D1CaseOneSmall3KF G) (h2 : D1CaseTwo3KF G) (h3 : D1CaseThree3KF G)
    (hweak : D1ConstrainedWeakBlockResidue3 G) : TheoremD1 G :=
  theoremD1_of_extremalCase3 hS (d1ExtremalCase3_of_cases_kFirst
    (fun hcomp => d1ConstrainedCaseInd3_of_phase3 hK3 hnone hcomp h84 hD2 hweak)
    (d1ComponentCaseKF3_of_cases hK3 h1s h2 h3))

end CFSG.LocalAnalysis.RankThreeTheoremC
