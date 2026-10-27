module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLHatMain
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneKFacts
import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroChar
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroAb
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem sq_le_card_of_not_isCyclic {p : ℕ} [Fact p.Prime] {X : Type*} [Group X] [Finite X]
    {T : Subgroup X} (hT : IsPGroup p T) (hnc : ¬ IsCyclic T) : p ^ 2 ≤ Nat.card T := by
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  have hp := (Fact.out : p.Prime)
  rcases n with _ | _ | n
  · exact absurd (by rw [pow_zero] at hn; exact (Subgroup.card_eq_one.mp hn) ▸
      (inferInstance : IsCyclic (⊥ : Subgroup X))) hnc
  · exact absurd (isCyclic_of_prime_card (p := p) (by rw [hn, pow_one])) hnc
  · rw [hn]
    exact Nat.pow_le_pow_right hp.pos (by omega)

theorem card_center_of_torusFacts {p : ℕ} [Fact p.Prime] {L : Type} [Group L] [Finite L]
    {T : Sylow p L} {n e : ℕ} (hTF : OneLieTorusFacts p L T n e) :
    Nat.card (centerOf (T : Subgroup L)) = p ^ n ∧ ∀ x ∈ centerOf (T : Subgroup L), x ^ p = 1 := by
  obtain ⟨ψ, hψinj, hψrange, -⟩ := hTF.torus
  have hn0 : n ≠ 0 := by have := hTF.two_le; omega
  have hrange : ψ.range = centerOf (T : Subgroup L) := hψrange
  refine ⟨?_, ?_⟩
  · rw [← hrange, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hψinj, Subgroup.card_top]
    change Nat.card (GaloisField p n) = p ^ n
    exact GaloisField.card p n hn0
  · intro x hx
    rw [← hrange] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [← map_pow]
    have : a ^ p = 1 := by
      change Multiplicative.ofAdd (p • Multiplicative.toAdd a) = 1
      rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
      rfl
    rw [this, map_one]

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.card_le_of_elem_inf [Fact p.Prime] (hd : D1OneSmallData p P M H R Rbar K)
    {z : G} (hz : D1SmallCZElt p H R K z) {P' : Sylow p G} {Pbar : Sylow p (D1CzQuot p z)}
    {KC : Subgroup (D1CzQuot p z)} (hRC : D1ReducedCentralizer p P' M z Pbar KC)
    (hzK : d1CzElt p z ∉ KC) {A : Subgroup (D1CzQuot p z)} (hA : IsElemAbelian p A)
    (hAR : A ≤ (R.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)))
    (hAK : A ≤ KC) : Nat.card A ≤ p ^ 2 := by
  have hp := hd.cfg.red.prime
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  set mk := QuotientGroup.mk' (primeComplementCore (G := C) p) with hmk
  have hOC := primeComplementCore_coprime (G := C) p
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hRC' : R ≤ C := hd.le_centralizer_czElt hz
  obtain ⟨hzZ, hzp⟩ := hRC.center ⟨z, hzC⟩ rfl
  set zt := mk ⟨z, hzC⟩ with hzt
  have hztK : zt ∉ KC := hzK
  have hztA : zt ∉ A := fun h => hztK (hAK h)
  have hztp : zt ^ p = 1 := by have h := pow_orderOf_eq_one zt; rwa [hzp] at h
  have hcomm : ∀ a ∈ A, a * zt = zt * a := fun a _ => Subgroup.mem_center_iff.mp hzZ a
  obtain ⟨hE, hcard⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers
    (A := A) ⟨hA.1, hA.2⟩ hztA hztp hcomm
  have hER : A ⊔ Subgroup.zpowers zt ≤ (R.subgroupOf C).map mk :=
    sup_le hAR (Subgroup.zpowers_le.mpr ⟨⟨z, hzC⟩, Subgroup.mem_subgroupOf.mpr hz.1, rfl⟩)
  have hEp : IsPGroup p (A ⊔ Subgroup.zpowers zt : Subgroup _) := fun g =>
    ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hrk : Open.pRank p ((R.subgroupOf C).map mk) = 3 := by
    rw [pRank_map_mk_eq_pRank_map_subtype hp _ hOC, Subgroup.map_subgroupOf_eq_of_le hRC']
    exact hd.pRank_R
  have hk3 : k ≤ 3 := by
    have := CFSG.SectionRank.le_pRank hp.one_lt hER ⟨hE.1, hE.2⟩ hk
    omega
  have h1 : Nat.card A * p ≤ p ^ 3 := by
    rw [← hcard, hk]
    exact Nat.pow_le_pow_right hp.pos hk3
  have h2 : p ^ 3 = p ^ 2 * p := by ring
  rw [h2] at h1
  exact Nat.le_of_mul_le_mul_right h1 hp.pos

theorem D1OneSmallData.map_d1LiftX_eq_center [Fact p.Prime] (hExp : KFactSmallSylowExp)
    (hβ : KFactBeta) (hKO : KFactOneLie) (hTor : KFactOneLieTorus) (hSch : KFactCatalogSchreier)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hout : D1CzOutside p z) (h3 : D1PhaseThree p P M H R)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥)
    {P' : Sylow p G} {Pbar : Sylow p (D1CzQuot p z)} {KC : Subgroup (D1CzQuot p z)}
    (hRC : D1ReducedCentralizer p P' M z Pbar KC) (hRP' : R ≤ P')
    (hP'M : (P' : Subgroup G) ≤ M) :
    ∃ (TC : Sylow p KC) (e : ℕ),
      (TC : Subgroup KC).map KC.subtype = (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC ∧
      OneLieTorusFacts p KC TC 2 e ∧
      ((d1LiftX p H R K).subgroupOf (Subgroup.centralizer ({z} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) =
        centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC) := by
  have hp := hd.cfg.red.prime
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  set mk := QuotientGroup.mk' (primeComplementCore (G := C) p) with hmk
  have hOC := primeComplementCore_coprime (G := C) p
  have hRC' : R ≤ C := hd.le_centralizer_czElt hz
  have hzK : d1CzElt p z ∉ KC := hout KC hRC.comp
  obtain ⟨T₁, n, e, hT₁, hTF, hle⟩ :=
    hd.center_le_map_R hβ hKO hTor hSch h84 hD2 hz hout h3 hY hRC hRP' hP'M
  set E := centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC) with hEdef
  have hEeq : E = (centerOf (T₁ : Subgroup KC)).map KC.subtype := by
    rw [map_subtype_centerOf, hT₁]
  obtain ⟨hcZ, hexpZ⟩ := card_center_of_torusFacts hTF
  have hEcard : Nat.card E = p ^ n := by
    rw [hEeq, Subgroup.card_map_of_injective KC.subtype_injective, hcZ]
  have hEK : E ≤ KC := by
    rw [hEeq]; exact Subgroup.map_subtype_le _
  have hEexp : ∀ x ∈ E, x ^ p = 1 := by
    intro x hx
    rw [hEeq] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← map_pow, hexpZ y hy, map_one]
  have hEab : IsMulCommutative E := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    simp only [Subgroup.coe_mul]
    exact (Subgroup.mem_centralizer_iff.mp a.2.2 b b.2.1).symm
  have hEle := hd.card_le_of_elem_inf hz hRC hzK ⟨hEab, hEexp⟩ hle hEK
  have hn2 : n = 2 := by
    have h1 : p ^ n ≤ p ^ 2 := hEcard ▸ hEle
    have h2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
    have := hTF.two_le
    omega
  subst hn2
  set Xt := ((d1LiftX p H R K).subgroupOf C).map mk with hXt
  have hXE : Xt ≤ E := by
    rintro _ ⟨⟨x, hxC⟩, hxX, rfl⟩
    have hxX' : x ∈ d1LiftX p H R K := Subgroup.mem_subgroupOf.mp hxX
    have hxK := hd.mk_mem_comp_of_mem_d1LiftX hz hRC hSch hxX' hxC
    have hxP : mk ⟨x, hxC⟩ ∈ (Pbar : Subgroup (D1CzQuot p z)) := by
      rw [hRC.sylow_eq]
      exact ⟨⟨x, hxC⟩, Subgroup.mem_subgroupOf.mpr (hRP' (d1LiftX_le p H R K hxX')), rfl⟩
    have hxR : mk ⟨x, hxC⟩ ∈ (R.subgroupOf C).map mk :=
      ⟨⟨x, hxC⟩, Subgroup.mem_subgroupOf.mpr (d1LiftX_le p H R K hxX'), rfl⟩
    have hxp : mk ⟨x, hxC⟩ ^ p = 1 := by
      have h1 : x ^ p = 1 := hd.pow_eq_one_of_mem_d1LiftX hExp hxX'
      have h2 : (⟨x, hxC⟩ : C) ^ p = 1 := Subtype.ext (by simpa using h1)
      rw [← map_pow, h2, map_one]
    by_contra hxE
    have hcomm : ∀ a ∈ E, a * mk ⟨x, hxC⟩ = mk ⟨x, hxC⟩ * a :=
      fun a ha => (Subgroup.mem_centralizer_iff.mp ha.2 _ ⟨hxP, hxK⟩).symm
    obtain ⟨hF, hFcard⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers
      (A := E) ⟨hEab, hEexp⟩ hxE hxp hcomm
    have hFR : E ⊔ Subgroup.zpowers (mk ⟨x, hxC⟩) ≤ (R.subgroupOf C).map mk :=
      sup_le hle (Subgroup.zpowers_le.mpr hxR)
    have hFK : E ⊔ Subgroup.zpowers (mk ⟨x, hxC⟩) ≤ KC :=
      sup_le hEK (Subgroup.zpowers_le.mpr hxK)
    have h1 := hd.card_le_of_elem_inf hz hRC hzK ⟨hF.1, hF.2⟩ hFR hFK
    rw [hFcard, hEcard] at h1
    have h2 : p ^ 2 * p ≤ p ^ 2 * 1 := by rw [mul_one]; exact h1
    have h3 := Nat.le_of_mul_le_mul_left h2 (pow_pos hp.pos 2)
    exact absurd h3 (by have := hp.two_le; omega)
  have hXcard : Nat.card Xt = Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      K : Subgroup _) := by
    have hXp : IsPGroup p ((d1LiftX p H R K).subgroupOf C) :=
      (hd.cfg.ext.isPGroup.to_le (d1LiftX_le p H R K)).comap_subtype
    rw [hXt, card_map_mk_of_isPGroup hp _ hOC hXp,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe ((d1LiftX_le p H R K).trans hRC')).toEquiv]
    exact (hd.d1LiftX_facts hz).2
  have hTp : IsPGroup p ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) := Rbar.isPGroup'.to_le inf_le_left
  have hge := sq_le_card_of_not_isCyclic hTp hd.noncyclic
  refine ⟨T₁, e, hT₁, hTF, Subgroup.eq_of_le_of_card_ge hXE ?_⟩
  rw [hEcard, hXcard]
  exact hge

end Config

end CFSG.AGLEmbedding
