module

public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedEscapeAux
public import CFSG.LocalAnalysis.AGLEmbedding.Extremal
public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedReduced

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1Escape.ne_sylow_of_hasPrimeConstraint (h : D1Escape p P M H R)
    (hcon : HasPrimeConstraint (G := H) p) (hP : 4 ≤ Open.pRank p (P : Subgroup G)) :
    R ≠ (P : Subgroup G) := by
  intro hRP
  have hR3 := (PreuniquenessRankFour.Helpers.pRank_mono p h.prime h.le_H).trans
    (pRank_le_three_of_escape_of_hasPrimeConstraint h.prime h.ne_two P h.sylow_le h.weakCore_le
      h.three_le_pRank_inf h.not_le hcon)
  rw [hRP] at hR3
  omega

theorem D1Escape.exists_isElemAbelian_normalizer_not_le (h : D1Escape p P M H R)
    (hcon : HasPrimeConstraint (G := H) p) :
    ∃ D : Subgroup G, D ≤ R ∧ IsElemAbelian p D ∧ Nat.card D = p ^ 2 ∧
      ¬ Subgroup.normalizer (D : Set G) ≤ M := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Rbar, hRbar, hred⟩ := h.reducedNongeneration
  obtain ⟨Q, hQn, hQp, hQc⟩ := hcon
  have : Q.Normal := hQn
  obtain ⟨Dbar, hDR, hD, hDcard, hDN⟩ := hred.exists_isElemAbelian_normalizer_not_le hQp hQc
  have hO : p.Coprime (Nat.card (primeComplementCore (G := H) p)) :=
    primeComplementCore_coprime p
  have hOM : primeComplementCore (G := H) p ≤ (H ⊓ M).subgroupOf H := by
    rw [← glbPrimeCore_subgroupOf]
    exact glbPrimeCore_subgroupOf_le_inf h.primeCore_le
  have hRp : IsPGroup p (R.subgroupOf H) := h.isPGroup.comap_subtype
  rw [hRbar] at hDR
  obtain ⟨D₁, hD₁R, hD₁map, hD₁, hD₁card⟩ := exists_isElemAbelian_lift hp _ hO hRp hD hDR
  refine ⟨D₁.map H.subtype,
    (Subgroup.map_mono hD₁R).trans (Subgroup.map_subgroupOf_eq_of_le h.le_H).le,
    elementary_abelian_map p hD₁ _,
    by rw [Subgroup.card_map_of_injective H.subtype_injective, hD₁card, hDcard], fun hN => hDN ?_⟩
  have hNH : Subgroup.normalizer (D₁ : Set H) ≤ (H ⊓ M).subgroupOf H := fun n hn =>
    Subgroup.mem_subgroupOf.mpr
      ⟨n.property, hN (Subgroup.le_normalizer_map H.subtype ⟨n, hn, rfl⟩)⟩
  rw [← hD₁map]
  exact le_map_of_comap_le (QuotientGroup.mk'_surjective _)
    ((comap_normalizer_map_le_sup hp _ hO (hRp.to_le hD₁R)).trans (sup_le hOM hNH))

theorem exists_mem_center_of_normalizer_not_le (hp : p.Prime) (hp2 : p ≠ 2) (P : Sylow p G)
    (hPM : (P : Subgroup G) ≤ M) (hWM : GLBWeakCore p (P : Subgroup G) ≤ M)
    (hP : 3 ≤ Open.pRank p (P : Subgroup G)) {D : Subgroup G} (hD : IsElemAbelian p D)
    (hDcard : Nat.card D = p ^ 2) (hDP : D ≤ P) (hDN : ¬ Subgroup.normalizer (D : Set G) ≤ M) :
    ∃ z : G, z ∈ D ∧ orderOf z = p ∧ z ∈ Subgroup.centralizer ((P : Subgroup G) : Set G) ∧
      ∀ y ∈ Subgroup.centralizer ((P : Subgroup G) : Set G), y ∈ (P : Subgroup G) →
        orderOf y = p → y ∈ Subgroup.zpowers z := by
  refine exists_mem_center_of_pRank_centralizer_le_two hp hp2 P.isPGroup' hP hD hDcard hDP ?_
  by_contra! h3
  exact hDN (normalizer_le_of_centralizer_rank_in_containing_sylow p hp P hPM hWM (hDP.trans hPM)
    (IsPGroup.of_card hDcard) (le_csSup (pRank_bddAbove p hp D) ⟨D, le_rfl, hD, hDcard⟩)
    ((show 3 ≤ Open.pRank p ((P : Subgroup G) ⊓ Subgroup.centralizer (D : Set G)) by omega).trans
      (PreuniquenessRankFour.Helpers.pRank_mono p hp (inf_le_inf_right _ hPM))))

theorem D1Escape.normalizer_zpowers_not_le (h : D1Escape p P M H R)
    (hcon : HasPrimeConstraint (G := H) p) {z : G} (hzR : z ∈ R)
    (hzc : z ∈ Subgroup.centralizer (R : Set G)) (hzp : orderOf z = p) :
    ¬ Subgroup.normalizer (Subgroup.zpowers z : Set G) ≤ M := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Rbar, hRbar, hred⟩ := h.reducedNongeneration
  obtain ⟨Q, hQn, hQp, hQc⟩ := hcon
  have : Q.Normal := hQn
  have hO : p.Coprime (Nat.card (primeComplementCore (G := H) p)) :=
    primeComplementCore_coprime p
  have hOM : primeComplementCore (G := H) p ≤ (H ⊓ M).subgroupOf H := by
    rw [← glbPrimeCore_subgroupOf]
    exact glbPrimeCore_subgroupOf_le_inf h.primeCore_le
  have hRp : IsPGroup p (R.subgroupOf H) := h.isPGroup.comap_subtype
  let zH : H := ⟨z, h.le_H hzR⟩
  have hzHp : orderOf zH = p := (Subgroup.orderOf_coe zH).symm.trans hzp
  have hzbar : QuotientGroup.mk' (primeComplementCore p) zH ∈
      Subgroup.centralizer (Q : Set (H ⧸ primeComplementCore (G := H) p)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' := hQp.le_sylow_of_normal Rbar hq
    rw [hRbar] at hq'
    obtain ⟨r, hr, rfl⟩ := hq'
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (Subgroup.mem_centralizer_iff.mp hzc r hr))
  have hzbarp : orderOf (QuotientGroup.mk' (primeComplementCore (G := H) p) zH) = p := by
    refine orderOf_eq_prime (by rw [← map_pow, ← hzHp, pow_orderOf_eq_one, map_one]) ?_
    intro h1
    have hzO : zH ∈ R.subgroupOf H ⊓ primeComplementCore p :=
      ⟨hzR, by rwa [← QuotientGroup.ker_mk' (primeComplementCore (G := H) p)]⟩
    rw [inf_eq_bot_of_isPGroup hp hRp hO, Subgroup.mem_bot] at hzO
    rw [hzO, orderOf_one] at hzHp
    exact hp.one_lt.ne hzHp
  have hnormal := zpowers_normal_of_mem_centralizer hQc
    (fun A hA hAe => by
      have := hA
      exact hred.card_le_of_normal_isElemAbelian hAe) hzbar hzbarp
  have hZp : IsPGroup p (Subgroup.zpowers zH) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzHp, pow_one])
  have hfr := comap_normalizer_map_le_sup hp _ hO hZp
  rw [MonoidHom.map_zpowers, Subgroup.normalizer_eq_top_iff.mpr hnormal,
    Subgroup.comap_top] at hfr
  intro hN
  have hNH : Subgroup.normalizer (Subgroup.zpowers zH : Set H) ≤ (H ⊓ M).subgroupOf H :=
    fun n hn => Subgroup.mem_subgroupOf.mpr ⟨n.property, hN (by
      have hmem := Subgroup.le_normalizer_map H.subtype ⟨n, hn, rfl⟩
      rwa [MonoidHom.map_zpowers] at hmem)⟩
  apply h.not_le
  intro g hg
  exact (Subgroup.mem_subgroupOf.mp ((hfr.trans (sup_le hOM hNH)) (Subgroup.mem_top ⟨g, hg⟩))).2

theorem D1Escape.centralizer_not_le_of_hasPrimeConstraint (h : D1Escape p P M H R)
    (hcon : HasPrimeConstraint (G := H) p) (hP : 3 ≤ Open.pRank p (P : Subgroup G)) {z : G}
    (hzR : z ∈ R) (hzc : z ∈ Subgroup.centralizer ((P : Subgroup G) : Set G))
    (hzp : orderOf z = p) :
    ¬ Subgroup.centralizer ({z} : Set G) ≤ M := by
  have : Fact p.Prime := ⟨h.prime⟩
  intro hCM
  refine h.normalizer_zpowers_not_le hcon hzR (Subgroup.centralizer_le h.le_P hzc) hzp
    (normalizer_zpowers_le P (fun x hx => ?_) hCM
      ((normalizer_le_weakCore_of_rank p h.prime _ hP).trans h.weakCore_le))
  exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzc x hx)

theorem D1Extremal.exists_central_of_hasPrimeConstraint {G : Type} [Group G] [Finite G]
    {p : ℕ} {P : Sylow p G} {M : Subgroup G} (hloc : D1Local p P M)
    {H R : Subgroup G} (h : D1Extremal p P M H R) (hcon : HasPrimeConstraint (G := H) p) :
    ∃ z : G, z ∈ R ∧ orderOf z = p ∧ z ∈ Subgroup.centralizer (P : Set G) ∧
      (∀ y ∈ Subgroup.centralizer (P : Set G), y ∈ (P : Subgroup G) → orderOf y = p →
        y ∈ Subgroup.zpowers z) ∧
      ¬ Subgroup.centralizer ({z} : Set G) ≤ M ∧
      GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ M ∧
      Odd (Nat.card (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)))) ∧
      CFSG.layer (Subgroup.centralizer ({z} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) ≠ ⊥ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hP4 : 4 ≤ Open.pRank p (P : Subgroup G) := betaFour_all_sylows_rank_ge_four hloc.beta P
  have hRP := h.toD1Escape.ne_sylow_of_hasPrimeConstraint hcon hP4
  obtain ⟨D, hDR, hD, hDcard, hDN⟩ := h.toD1Escape.exists_isElemAbelian_normalizer_not_le hcon
  obtain ⟨z, hzD, hzp, hzc, huniq⟩ := exists_mem_center_of_normalizer_not_le hp h.ne_two P
    h.sylow_le h.weakCore_le (by omega) hD hDcard (hDR.trans h.le_P) hDN
  have hzR := hDR hzD
  have hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzc x hx)
  have hCM := h.toD1Escape.centralizer_not_le_of_hasPrimeConstraint hcon (by omega) hzR hzc hzp
  have hcoreM : GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ M :=
    intersecting_local_primeCore_le p hp P h.sylow_le h.weakCore_le
      ((show 3 ≤ Open.pRank p (P : Subgroup G) by omega).trans
        (PreuniquenessRankFour.Helpers.pRank_mono p hp (le_inf hPC h.sylow_le)))
  refine ⟨z, hzR, hzp, hzc, huniq, hCM, hcoreM, ?_, ?_⟩
  · exact odd_card_of_twoLocals_le hp P.isPGroup' hPC hCM (glbPrimeCore_le p _)
      (glbPrimeCore_normal p _) (glbPrimeCore_coprime p _) hcoreM
      fun T hT hT1 hPT => h.normalizer_le_of_sylow_le hRP hT hT1 hPT
  ·
    refine layer_ne_bot_of_four_le_pRank hp h.ne_two P h.sylow_le h.weakCore_le hCM
      (P.subtype hPC) ?_ ?_ hcoreM
    · rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPC]
    · rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPC]
      exact hP4

end CFSG.AGLEmbedding
