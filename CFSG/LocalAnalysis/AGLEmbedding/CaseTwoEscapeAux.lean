module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieDefs
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReducedBAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Centralizer

variable {G : Type} [Group G] [Finite G] {p : ℕ}

structure D1ReducedCentralizer (p : ℕ) (P : Sylow p G) (M : Subgroup G) (z : G)
    (Pbar : Sylow p (Subgroup.centralizer ({z} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p))
    (K : Subgroup (Subgroup.centralizer ({z} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) : Prop where
  sylow_eq : (Pbar : Subgroup _) = ((P : Subgroup G).subgroupOf
    (Subgroup.centralizer ({z} : Set G))).map (QuotientGroup.mk' (primeComplementCore p))
  red : ReducedNongeneration p (Subgroup.centralizer ({z} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) Pbar
    (((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf
      (Subgroup.centralizer ({z} : Set G))).map (QuotientGroup.mk' (primeComplementCore p)))
  four_le_pRank : 4 ≤ Open.pRank p (Pbar : Subgroup (Subgroup.centralizer ({z} : Set G) ⧸
    primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p))
  catalog : CatalogSimpleSections (Subgroup.centralizer ({z} : Set G) ⧸
    primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)
  center : ∀ zC : Subgroup.centralizer ({z} : Set G), (zC : G) = z →
    QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) zC ∈
      Subgroup.center (Subgroup.centralizer ({z} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) ∧
    orderOf (QuotientGroup.mk'
      (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) zC) = p
  comp : IsComponentOf K ⊤
  normal : K.Normal
  unique : ∀ L : Subgroup (Subgroup.centralizer ({z} : Set G) ⧸
    primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p), IsComponentOf L ⊤ → L = K

theorem exists_d1ReducedCentralizer {P : Sylow p G} {M : Subgroup G} (hglob : D1Global G)
    (hloc : D1Local p P M) (hPM : (P : Subgroup G) ≤ M) {z : G}
    (hzc : z ∈ Subgroup.centralizer (P : Set G)) (hzp : orderOf z = p)
    (hCM : ¬ Subgroup.centralizer ({z} : Set G) ≤ M) :
    ∃ (Pbar : Sylow p (Subgroup.centralizer ({z} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p))
      (K : Subgroup (Subgroup.centralizer ({z} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)),
      D1ReducedCentralizer p P M z Pbar K := by
  have hp : p.Prime := hloc.beta.1
  have hp2 : p ≠ 2 := hloc.beta.2.1
  have h4 : 4 ≤ Open.pRank p (P : Subgroup G) := betaFour_all_sylows_rank_ge_four hloc.beta P
  have hO := primeComplementCore_coprime (G := Subgroup.centralizer ({z} : Set G)) p
  have hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzc x hx)
  have hcore : GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ M :=
    intersecting_local_primeCore_le p hp P hPM hloc.core
      ((show 3 ≤ Open.pRank p (P : Subgroup G) by omega).trans
        (PreuniquenessRankFour.Helpers.pRank_mono p hp (le_inf hPC hPM)))
  obtain ⟨Pbar, hPbar, hred, hzbar⟩ := reducedNongeneration_centralizer_of_not_le hp hp2 P hPM
    hloc.core (by omega) hzc hzp hCM hcore
  obtain ⟨hzZ, hzbarp⟩ := hzbar ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ rfl
  have hPmap : ((P.subtype hPC : Sylow p _) : Subgroup _).map
      (Subgroup.centralizer ({z} : Set G)).subtype = P := by
    rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPC]
  have hlayer := layer_ne_bot_of_four_le_pRank hp hp2 P hPM hloc.core hCM (P.subtype hPC)
    hPmap.le (hPmap ▸ h4) hcore
  obtain ⟨K, hK⟩ := exists_isComponentOf_of_layer_ne_bot hlayer
  have hz1 : z ≠ 1 := fun hz1 => hp.one_lt.ne (by rw [← hzp, hz1, orderOf_one])
  refine ⟨Pbar, K, hPbar, hred, ?_, ?_, hzbar, hK,
    hred.normal_of_isComponentOf_of_center hzZ hzbarp hK,
    fun L hL => hred.eq_of_isComponentOf_of_center hzZ hzbarp hL hK⟩
  · rw [hPbar, pRank_map_mk_eq_pRank_map_subtype hp _ hO, Subgroup.map_subgroupOf_eq_of_le hPC]
    exact h4
  · exact (catalogSimpleSections_of_isKProper hglob.kProper _
      (centralizer_singleton_ne_top hglob.simple hglob.nonab hz1)).quotient _

theorem mem_centralizer_of_forall_exists_zpow (hp : p.Prime) (hp2 : p ≠ 2) {P M : Subgroup G}
    (hP : IsPGroup p P) (hPM : P ≤ M) {e : G} (heP : e ∈ P) (heY : e ∈ pCorePreimage p M)
    (hep : orderOf e = p)
    (hK : ∀ y ∈ pCorePreimage p M, y ^ p = 1 → ∃ k : ℤ, (e ^ k)⁻¹ * y ∈ pCoreOf 2 M) :
    e ∈ Subgroup.centralizer (P : Set G) := by
  have hcop : p.Coprime (Nat.card (pCoreOf 2 M)) := by
    obtain ⟨k, hk⟩ :=
      IsPGroup.iff_card.mp (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
    exact hk ▸ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right k
  have hbot : P ⊓ pCoreOf 2 M = ⊥ := inf_eq_bot_of_isPGroup hp hP hcop
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hy : x * e * x⁻¹ ∈ pCorePreimage p M :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCorePreimage p M (hPM hx)) e).mp heY
  have hyp : (x * e * x⁻¹) ^ p = 1 := by
    rw [conj_pow, ← hep, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  obtain ⟨k, hk⟩ := hK _ hy hyp
  have hq : (e ^ k)⁻¹ * (x * e * x⁻¹) ∈ P ⊓ pCoreOf 2 M :=
    ⟨P.mul_mem (P.inv_mem (P.zpow_mem heP k)) (P.mul_mem (P.mul_mem hx heP) (P.inv_mem hx)), hk⟩
  rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hq
  have hxN : x ∈ Subgroup.normalizer (Subgroup.zpowers e : Set G) :=
    mem_normalizer_zpowers_of_mem_zpowers (hq ▸ Subgroup.zpow_mem_zpowers e k)
  obtain ⟨n, hn⟩ := hP ⟨x, hx⟩
  have hxn : x ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
  exact (commute_of_mem_normalizer_zpowers_of_pow_prime_pow hp hep hxN hxn).eq

omit [Finite G] in
theorem le_normalizer_zpowers_sup_of_forall_exists_zpow {M : Subgroup G} {e : G}
    (heY : e ∈ pCorePreimage p M) (hep : e ^ p = 1)
    (hK : ∀ y ∈ pCorePreimage p M, y ^ p = 1 → ∃ k : ℤ, (e ^ k)⁻¹ * y ∈ pCoreOf 2 M) :
    M ≤ Subgroup.normalizer ((Subgroup.zpowers e ⊔ pCoreOf 2 M : Subgroup G) : Set G) := by
  refine le_normalizer_of_forall_map_conj_le fun m hm => ?_
  rw [Subgroup.map_sup, MonoidHom.map_zpowers]
  refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
  · have hy : m * e * m⁻¹ ∈ pCorePreimage p M :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCorePreimage p M hm) e).mp heY
    obtain ⟨k, hk⟩ := hK _ hy (by rw [conj_pow, hep, mul_one, mul_inv_cancel])
    rw [show (MulAut.conj m).toMonoidHom e = e ^ k * ((e ^ k)⁻¹ * (m * e * m⁻¹)) by
      rw [mul_inv_cancel_left]; rfl]
    exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers e k) hk
  · rintro _ ⟨q, hq, rfl⟩
    exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
      (localGroup_le_normalizer_pCoreOf 2 M hm) q).mp hq)

theorem exists_mem_centralizer_mk_eq {Y : Type*} [Group Y] [Finite Y] (hp : p.Prime)
    (O : Subgroup Y) [O.Normal] (hO : p.Coprime (Nat.card O)) {e : Y}
    (he : IsPGroup p (Subgroup.zpowers e)) {x : Y ⧸ O}
    (hx : x ∈ Subgroup.centralizer ({QuotientGroup.mk' O e} : Set (Y ⧸ O))) :
    ∃ g ∈ Subgroup.centralizer ({e} : Set Y), QuotientGroup.mk' O g = x := by
  have hcomm : x * QuotientGroup.mk' O e = QuotientGroup.mk' O e * x :=
    Subgroup.mem_centralizer_singleton_iff.mp hx
  have hxN : x ∈ Subgroup.normalizer (((Subgroup.zpowers e).map (QuotientGroup.mk' O) :
      Subgroup (Y ⧸ O)) : Set (Y ⧸ O)) := by
    rw [MonoidHom.map_zpowers]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (Commute.zpow_left hcomm.symm k).eq
  obtain ⟨g, -, rfl, hge⟩ := exists_mem_normalizer_mk_eq_commute hp O hO he hxN
    (Subgroup.mem_zpowers e) hcomm
  exact ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr hge, rfl⟩

end Centralizer

section PhaseThree

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1PhaseThree.exists_zpow_inv_mul_mem_twoCore (h : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) {e : H} (he : (e : G) ∈ pCorePreimage p M)
    (hΩ : ∀ v ∈ d1MapPCore p M H, v ^ p = 1 →
      v ∈ Subgroup.zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p) e))
    {y : G} (hy : y ∈ pCorePreimage p M) (hyp : y ^ p ∈ pCoreOf 2 M) :
    ∃ k : ℤ, ((e : G) ^ k)⁻¹ * y ∈ pCoreOf 2 M := by
  have hyH : y ∈ H := ((h.pCorePreimage_le_inf h84 hD2) hy).1
  have hyV : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨y, hyH⟩ ∈ d1MapPCore p M H :=
    Subgroup.mem_map_of_mem _ (show (⟨y, hyH⟩ : H) ∈ (pCorePreimage p M).subgroupOf H from hy)
  have hyp' : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨y, hyH⟩ ^ p = 1 := by
    rw [← map_pow]
    exact (mk'_primeComplementCore_eq_one_iff p _).mpr
      (by simpa using h.twoCore_M_le_glbPrimeCore hyp)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hΩ _ hyV hyp')
  refine ⟨k, h.pCorePreimage_inf_le ⟨(pCorePreimage p M).mul_mem
    ((pCorePreimage p M).inv_mem ((pCorePreimage p M).zpow_mem he k)) hy, ?_⟩⟩
  have h1 := (mk'_primeComplementCore_eq_one_iff p ((e ^ k)⁻¹ * ⟨y, hyH⟩)).mp
    (by rw [map_mul, map_inv, map_zpow, hk, inv_mul_cancel])
  simpa using h1

end PhaseThree

end CFSG.AGLEmbedding
