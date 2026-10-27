module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeAux
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReducedB
import CFSG.LocalAnalysis.AGLEmbedding.OneLieOpMbar
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDataAt

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoDataAt.d1MapPCore_le_inf_centralizer (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1CaseTwoDataAt p P M H R Rbar) {L : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hL : IsComponentOf L ⊤) (hLX₀ : ¬ L ≤ d1X0 p M H)
    (hVL : d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L) = ⊥) :
    d1MapPCore p M H ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      Subgroup.centralizer (L : Set (H ⧸ primeComplementCore (G := H) p)) := by
  have h3 := hd.toPhaseThree hAut hS hKL
  have hYH : pCorePreimage p M ≤ H := (h3.pCorePreimage_le_inf h84 hD2).trans inf_le_left
  have hVR : d1MapPCore p M H ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    rw [h3.d1MapPCore_eq h84 hD2, hd.cfg.rbar]
    exact Subgroup.map_mono (Subgroup.comap_mono inf_le_left)
  have hVn : d1X0 p M H ≤
      Subgroup.normalizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p)) :=
    map_le_normalizer_map _ hYH (inf_le_right.trans (le_normalizer_pCorePreimage p M))
  exact le_inf hVR (hd.cfg.red.le_centralizer_of_inf_eq_bot hKL hd.cyclic hL
    (hd.cfg.red.isCaseTwoGroup_of_not_le_of_aut hd.cfg.catalog (hAut _ _ _ _ hd.cfg.red
        hd.cfg.catalog) hS hd.cyclic hd.rank hL hLX₀)
    (fun t ht htp => hd.cfg.red.inf_normalizer_zpowers_le_of_aut (hAut _ _ _ _ hd.cfg.red
        hd.cfg.catalog) hd.cyclic hd.rank hL
      ht htp) hVR hVn hVL)

theorem D1CaseTwoData.d1MapPCore_le_inf_centralizer (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1CaseTwoData p P M H R Rbar) {L : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hL : IsComponentOf L ⊤) (hLX₀ : ¬ L ≤ d1X0 p M H)
    (hVL : d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L) = ⊥) :
    d1MapPCore p M H ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      Subgroup.centralizer (L : Set (H ⧸ primeComplementCore (G := H) p)) :=
  D1CaseTwoDataAt.d1MapPCore_le_inf_centralizer (hAut := (kFactCycAut_of_kFactBeta hβ)) (hS := hS)
    (hKL := hKL) (h84 := h84) (hD2 := hD2) (hd := hd.toAt) (hL := hL) (hLX₀ := hLX₀) (hVL := hVL)

theorem D1CaseTwoDataAt.isCyclic_d1MapPCore (hd : D1CaseTwoDataAt p P M H R Rbar)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (hLX₀ : ¬ L ≤ d1X0 p M H)
    (hVC : d1MapPCore p M H ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      Subgroup.centralizer (L : Set (H ⧸ primeComplementCore (G := H) p))) :
    IsCyclic (d1MapPCore p M H) := by
  have hp := hd.cfg.red.prime
  by_contra hnc
  have h2 := two_le_pRank_of_isPGroup_not_isCyclic hp hd.cfg.red.ne_two
    (Rbar.isPGroup'.to_le (hVC.trans inf_le_left)) hnc
  have h1 := hd.cfg.red.pRank_inf_centralizer_le_one_of_not_le hL hLX₀
  have h3 := PreuniquenessRankFour.Helpers.pRank_mono p hp hVC
  omega

theorem D1CaseTwoData.isCyclic_d1MapPCore (hd : D1CaseTwoData p P M H R Rbar)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (hLX₀ : ¬ L ≤ d1X0 p M H)
    (hVC : d1MapPCore p M H ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      Subgroup.centralizer (L : Set (H ⧸ primeComplementCore (G := H) p))) :
    IsCyclic (d1MapPCore p M H) :=
  D1CaseTwoDataAt.isCyclic_d1MapPCore (hd := hd.toAt) (hL := hL) (hLX₀ := hLX₀) (hVC := hVC)

theorem D1CaseTwoDataAt.exists_escape_elt (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1CaseTwoDataAt p P M H R Rbar) {L : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hL : IsComponentOf L ⊤) (hLX₀ : ¬ L ≤ d1X0 p M H)
    (hVL : d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L) = ⊥)
    (hV : pCorePreimage p M ⊓ R ≠ ⊥) :
    ∃ e : H, (e : G) ∈ R ∧ (e : G) ∈ pCorePreimage p M ∧ orderOf (e : G) = p ∧
      (∀ v ∈ d1MapPCore p M H, v ^ p = 1 →
        v ∈ Subgroup.zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p) e)) ∧
      (∀ y ∈ pCorePreimage p M, y ^ p ∈ pCoreOf 2 M →
        ∃ k : ℤ, ((e : G) ^ k)⁻¹ * y ∈ pCoreOf 2 M) ∧
      (e : G) ∈ Subgroup.centralizer (P : Set G) ∧
      QuotientGroup.mk' (primeComplementCore (G := H) p) e ∈
        Subgroup.centralizer (L : Set (H ⧸ primeComplementCore (G := H) p)) := by
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have h3 := hd.toPhaseThree hAut hS hKL
  have hO := primeComplementCore_coprime (G := H) p
  have hVC := hd.d1MapPCore_le_inf_centralizer hAut hS hKL h84 hD2 hL hLX₀ hVL
  have hcyc := hd.isCyclic_d1MapPCore hL hLX₀ hVC
  have hXp : IsPGroup p (R ⊓ pCorePreimage p M : Subgroup G) :=
    hd.cfg.ext.isPGroup.to_le inf_le_left
  obtain ⟨e₀, he₀⟩ : ∃ x : (R ⊓ pCorePreimage p M : Subgroup G), orderOf x = p := by
    refine exists_prime_orderOf_dvd_card' p ?_
    rcases hXp.card_eq_or_dvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) (by rwa [inf_comm])
    · exact h1
  have heX : (e₀ : G) ∈ R ⊓ pCorePreimage p M := e₀.2
  have hep : orderOf (e₀ : G) = p := (Subgroup.orderOf_coe e₀).trans he₀
  set e : H := ⟨e₀, hd.cfg.ext.le_H heX.1⟩
  have heH : orderOf e = p := (Subgroup.orderOf_coe e).symm.trans hep
  have hemp : orderOf (QuotientGroup.mk' (primeComplementCore (G := H) p) e) = p :=
    orderOf_mk_of_coprime hp _ hO heH
  have hemV : QuotientGroup.mk' (primeComplementCore (G := H) p) e ∈ d1MapPCore p M H :=
    Subgroup.mem_map_of_mem _ (show e ∈ (pCorePreimage p M).subgroupOf H from heX.2)
  have hΩ : ∀ v ∈ d1MapPCore p M H, v ^ p = 1 →
      v ∈ Subgroup.zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p) e) := by
    intro v hv hvp
    by_cases hv1 : v = 1
    · rw [hv1]
      exact Subgroup.one_mem _
    · exact mem_zpowers_of_orderOf_eq_of_isCyclic hv hemV
        (by rw [orderOf_eq_prime hvp hv1, hemp])
  have hK : ∀ y ∈ pCorePreimage p M, y ^ p ∈ pCoreOf 2 M →
      ∃ k : ℤ, ((e : G) ^ k)⁻¹ * y ∈ pCoreOf 2 M :=
    fun y hy hyp => h3.exists_zpow_inv_mul_mem_twoCore h84 hD2 heX.2 hΩ hy hyp
  have hcen := mem_centralizer_of_forall_exists_zpow hp hp2 P.isPGroup' hd.cfg.ext.sylow_le
    (hd.cfg.ext.le_P heX.1) heX.2 hep fun y hy hyp => hK y hy (hyp ▸ (pCoreOf 2 M).one_mem)
  exact ⟨e, heX.1, heX.2, hep, hΩ, hK, hcen, (hVC hemV).2⟩

structure D1CaseTwoEscapeData (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (L : Subgroup (H ⧸ primeComplementCore (G := H) p)) (e : H) : Prop where
  data : D1CaseTwoData p P M H R Rbar
  comp : IsComponentOf L ⊤
  not_le : ¬ L ≤ d1X0 p M H
  isCaseTwoGroup : IsCaseTwoGroup p L
  le_inf_centralizer : d1MapPCore p M H ≤
    (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      Subgroup.centralizer (L : Set (H ⧸ primeComplementCore (G := H) p))
  isCyclic : IsCyclic (d1MapPCore p M H)
  mem_R : (e : G) ∈ R
  mem_pCorePreimage : (e : G) ∈ pCorePreimage p M
  orderOf_eq : orderOf (e : G) = p
  mem_zpowers_mk : ∀ v ∈ d1MapPCore p M H, v ^ p = 1 →
    v ∈ Subgroup.zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p) e)
  mem_zpowers_sup : ∀ y ∈ pCorePreimage p M, y ^ p ∈ pCoreOf 2 M →
    y ∈ Subgroup.zpowers (e : G) ⊔ pCoreOf 2 M
  le_normalizer : M ≤ Subgroup.normalizer
    ((Subgroup.zpowers (e : G) ⊔ pCoreOf 2 M : Subgroup G) : Set G)
  mem_centralizer : (e : G) ∈ Subgroup.centralizer (P : Set G)
  centralizer_not_le : ¬ Subgroup.centralizer ({(e : G)} : Set G) ≤ M
  primeCore_le : GLBPrimeCore p (Subgroup.centralizer ({(e : G)} : Set G)) ≤ M

theorem D1CaseTwoData.exists_escapeData (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1CaseTwoData p P M H R Rbar) {L : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hL : IsComponentOf L ⊤) (hLX₀ : ¬ L ≤ d1X0 p M H)
    (hVL : d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L) = ⊥)
    (hV : pCorePreimage p M ⊓ R ≠ ⊥) :
    ∃ e : H, D1CaseTwoEscapeData p P M H R Rbar L e := by
  have hp := hd.cfg.red.prime
  have hO := primeComplementCore_coprime (G := H) p
  have hVC := hd.d1MapPCore_le_inf_centralizer hβ hS hKL h84 hD2 hL hLX₀ hVL
  have hcyc := hd.isCyclic_d1MapPCore hL hLX₀ hVC
  obtain ⟨e, heR, heY, hep, hΩ, hK, hcen, heL⟩ := hd.toAt.exists_escape_elt
    (kFactCycAut_of_kFactBeta hβ) hS hKL h84 hD2 hL hLX₀ hVL hV
  have heH : orderOf e = p := (Subgroup.orderOf_coe e).symm.trans hep
  have hK1 : ∀ y ∈ pCorePreimage p M, y ^ p = 1 →
      ∃ k : ℤ, ((e : G) ^ k)⁻¹ * y ∈ pCoreOf 2 M :=
    fun y hy hyp => hK y hy (hyp ▸ (pCoreOf 2 M).one_mem)
  have hsup : ∀ y ∈ pCorePreimage p M, y ^ p ∈ pCoreOf 2 M →
      y ∈ Subgroup.zpowers (e : G) ⊔ pCoreOf 2 M := by
    intro y hy hyp
    obtain ⟨k, hk⟩ := hK y hy hyp
    rw [← mul_inv_cancel_left ((e : G) ^ k) y]
    exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers _ k) hk
  have hnorm := le_normalizer_zpowers_sup_of_forall_exists_zpow heY
    (orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hep)) hK1
  have hCM : ¬ Subgroup.centralizer ({(e : G)} : Set G) ≤ M := by
    obtain ⟨ℓ, hℓL, hℓX₀⟩ := Set.not_subset.mp hLX₀
    obtain ⟨g, hg, rfl⟩ := exists_mem_centralizer_mk_eq hp _ hO
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, heH, pow_one]))
      (Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp heL ℓ hℓL))
    have hgC : (g : G) ∈ Subgroup.centralizer ({(e : G)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg))
    exact fun hle => hℓX₀ ⟨g, ⟨g.2, hle hgC⟩, rfl⟩
  have hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({(e : G)} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hcen x hx)
  have h4 := betaFour_all_sylows_rank_ge_four hd.cfg.loc.beta P
  have hcore : GLBPrimeCore p (Subgroup.centralizer ({(e : G)} : Set G)) ≤ M :=
    intersecting_local_primeCore_le p hp P hd.cfg.ext.sylow_le hd.cfg.ext.weakCore_le
      ((show 3 ≤ Open.pRank p (P : Subgroup G) by omega).trans
        (PreuniquenessRankFour.Helpers.pRank_mono p hp (le_inf hPC hd.cfg.ext.sylow_le)))
  exact ⟨e, hd, hL, hLX₀,
    hd.cfg.red.isCaseTwoGroup_of_not_le hd.cfg.catalog hβ hS hd.cyclic hd.rank hL hLX₀, hVC, hcyc,
    heR, heY, hep, hΩ, hsup, hnorm, hcen, hCM, hcore⟩

variable {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} {e : H}

theorem D1CaseTwoEscapeData.mk_mem_centralizer (he : D1CaseTwoEscapeData p P M H R Rbar L e) :
    QuotientGroup.mk' (primeComplementCore (G := H) p) e ∈
      Subgroup.centralizer (L : Set (H ⧸ primeComplementCore (G := H) p)) :=
  (he.le_inf_centralizer (Subgroup.mem_map_of_mem _
    (show e ∈ (pCorePreimage p M).subgroupOf H from he.mem_pCorePreimage))).2

theorem D1CaseTwoEscapeData.le_centralizer_mk (he : D1CaseTwoEscapeData p P M H R Rbar L e) :
    L ≤ Subgroup.centralizer ({QuotientGroup.mk' (primeComplementCore (G := H) p) e} :
      Set (H ⧸ primeComplementCore (G := H) p)) := fun l hl =>
  Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp he.mk_mem_centralizer l hl)

theorem D1CaseTwoEscapeData.exists_lift (he : D1CaseTwoEscapeData p P M H R Rbar L e)
    {x : H ⧸ primeComplementCore (G := H) p}
    (hx : x ∈ Subgroup.centralizer ({QuotientGroup.mk' (primeComplementCore (G := H) p) e} :
      Set (H ⧸ primeComplementCore (G := H) p))) :
    ∃ g : H, (g : G) ∈ Subgroup.centralizer ({(e : G)} : Set G) ∧
      QuotientGroup.mk' (primeComplementCore (G := H) p) g = x := by
  have heH : orderOf e = p := (Subgroup.orderOf_coe e).symm.trans he.orderOf_eq
  obtain ⟨g, hg, rfl⟩ := exists_mem_centralizer_mk_eq he.data.cfg.red.prime _
    (primeComplementCore_coprime p)
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, heH, pow_one])) hx
  exact ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg)), rfl⟩

theorem D1CaseTwoEscapeData.exists_reducedCentralizer
    (he : D1CaseTwoEscapeData p P M H R Rbar L e) :
    ∃ (Pbar : Sylow p (Subgroup.centralizer ({(e : G)} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({(e : G)} : Set G)) p))
      (K : Subgroup (Subgroup.centralizer ({(e : G)} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({(e : G)} : Set G)) p)),
      D1ReducedCentralizer p P M (e : G) Pbar K :=
  exists_d1ReducedCentralizer he.data.cfg.glob he.data.cfg.loc he.data.cfg.ext.sylow_le
    he.mem_centralizer he.orderOf_eq he.centralizer_not_le

end Data

end CFSG.AGLEmbedding
