module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUnitaryZData
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoDataAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMData
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMDataAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMDataAux2
import CFSG.LocalAnalysis.AGLEmbedding.OneLieOpMbar
import CFSG.LocalAnalysis.AGLEmbedding.OneLieTorusFamilies
import CFSG.LocalAnalysis.AGLEmbedding.OneLieUnitaryZAux
import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section PCore

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {P : Sylow p G}
  {M H R : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneLieData.unitary_pCore (hK : KFactOneLie) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1OneLieData p P M H R Rbar K) {T₁ : Sylow p K}
    (hT₁ : (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) (hF : OneLieFacts p K T₁)
    {c : K} (hcN : c ∈ Subgroup.normalizer ((T₁ : Subgroup K) : Set K))
    (hcnt : ∃ u ∈ (T₁ : Subgroup K), c * u * c⁻¹ * u⁻¹ ∉
      (T₁ : Subgroup K) ⊓ Subgroup.centralizer ((T₁ : Subgroup K) : Set K))
    (hcirr : ∀ V : Subgroup K,
      (T₁ : Subgroup K) ⊓ Subgroup.centralizer ((T₁ : Subgroup K) : Set K) ≤ V →
      V ≤ T₁ → c ∈ Subgroup.normalizer (V : Set K) →
      V = (T₁ : Subgroup K) ⊓ Subgroup.centralizer ((T₁ : Subgroup K) : Set K) ∨ V = T₁)
    (hZ : d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
      centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) :
    d1LiftX p H R (centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) ≤
        pCorePreimage p M ∧
      d1LiftX p H R K ⊓ pCorePreimage p M ≤
        d1LiftX p H R (centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) ∧
      ∀ x ∈ d1LiftX p H R K, ∀ y ∈ R ⊓ pCorePreimage p M, x * y = y * x := by
  have hp : p.Prime := Fact.out
  have h3 := hd.toPhaseThree hK
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  have : (Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))).Normal :=
    Subgroup.normal_centralizer
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set T : Subgroup (H ⧸ primeComplementCore (G := H) p) :=
    (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K with hTdef
  set W := d1MapPCore p M H with hW
  set U := d1LiftX p H R K with hUdef
  set Z := d1LiftX p H R (centerOf T) with hZdef
  obtain ⟨hWp, hWR, hWn, -, -⟩ := hd.d1MapPCore_facts hK h84 hD2
  have hWTC : W ≤ T ⊔ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) :=
    (le_sup_of_oneLieFacts hd.center T₁ hT₁ hF hWp hWR hWn).trans
      (sup_le_sup_left inf_le_right _)
  have hZT : centerOf T =
      ((T₁ : Subgroup K) ⊓ Subgroup.centralizer ((T₁ : Subgroup K) : Set K)).map K.subtype := by
    rw [← hT₁]
    exact (map_subtype_centerOf _).symm
  have hcY : (c : H ⧸ primeComplementCore (G := H) p) ∈
      K ⊓ Subgroup.normalizer (T : Set (H ⧸ primeComplementCore (G := H) p)) := by
    have := coe_mem_normalizer_map hcN
    rwa [hT₁] at this
  have hcomm : ∀ w ∈ W, ∀ x ∈ T, w * x = x * w := by
    refine forall_mul_comm_of_inf_eq_centerOf inf_le_right hWTC hZ hcY.1 hcY.2 (hWn hcY) ?_ ?_
    · obtain ⟨u₁, hu₁T, hu₁Z⟩ := hcnt
      refine ⟨u₁, hT₁ ▸ ⟨u₁, hu₁T, rfl⟩, fun hmem => hu₁Z ?_⟩
      rw [hZT] at hmem
      have hmem' : K.subtype (c * u₁ * c⁻¹ * u₁⁻¹) ∈
          ((T₁ : Subgroup K) ⊓ Subgroup.centralizer ((T₁ : Subgroup K) : Set K)).map
            K.subtype := by
        simpa using hmem
      exact (Subgroup.mem_map_iff_mem K.subtype_injective).mp hmem'
    · intro V' hZV' hVT hcV'
      have hVK : V' ≤ K := hVT.trans inf_le_right
      have hWmap : (V'.subgroupOf K).map K.subtype = V' := Subgroup.map_subgroupOf_eq_of_le hVK
      have hZW : (T₁ : Subgroup K) ⊓ Subgroup.centralizer ((T₁ : Subgroup K) : Set K) ≤
          V'.subgroupOf K := fun x hx =>
        Subgroup.mem_subgroupOf.mpr (hZV' (hZT ▸ ⟨x, hx, rfl⟩))
      have hWT : V'.subgroupOf K ≤ T₁ := by
        intro x hx
        have h1 : (x : H ⧸ primeComplementCore (G := H) p) ∈ T :=
          hVT (Subgroup.mem_subgroupOf.mp hx)
        rw [← hT₁] at h1
        exact (Subgroup.mem_map_iff_mem K.subtype_injective).mp h1
      have hcW : c ∈ Subgroup.normalizer ((V'.subgroupOf K : Subgroup K) : Set K) :=
        Subgroup.le_normalizer_comap K.subtype (show K.subtype c ∈ _ from hcV')
      rcases hcirr _ hZW hWT hcW with h | h
      · left
        rw [← hWmap, h, hZT]
      · right
        rw [← hWmap, h, hT₁]
  have hRH : R ≤ H := hd.cfg.ext.le_H
  have hRp : IsPGroup p R := hd.cfg.ext.isPGroup
  have hRN : R ⊓ GLBPrimeCore p H = ⊥ := inf_eq_bot_of_isPGroup hp hRp (glbPrimeCore_coprime p H)
  have hUR : U ≤ R := d1LiftX_le p H R K
  have hZR : Z ≤ R := d1LiftX_le p H R _
  have hUmap : (U.subgroupOf H).map π = T := hd.cfg.map_d1LiftX_eq_inf
  have hZmap : (Z.subgroupOf H).map π = centerOf T := hd.map_d1LiftX_centerOf
  have hWeq : W = ((R ⊓ pCorePreimage p M).subgroupOf H).map π := h3.d1MapPCore_eq h84 hD2
  have hYH : pCorePreimage p M ≤ H := (h3.pCorePreimage_le_inf h84 hD2).trans inf_le_left
  refine ⟨fun z hz => ?_, ?_, fun x hx y hy => ?_⟩
  · have hle : Z ≤ R ⊓ pCorePreimage p M := by
      refine le_of_map_mk_le_of_isPGroup hRH hRp hZR inf_le_left ?_
      rw [hZmap, ← hWeq, ← hZ]
      exact inf_le_left
    exact (hle hz).2
  · refine le_of_map_mk_le_of_isPGroup hRH hRp (inf_le_left.trans hUR) hZR ?_
    rintro _ ⟨a, ha, rfl⟩
    have haU : π a ∈ T := hUmap ▸ ⟨a, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_subgroupOf.mp ha).1, rfl⟩
    have haW : π a ∈ W := ⟨a, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp ha).2, rfl⟩
    rw [hZmap, ← hZ]
    exact ⟨haW, haU⟩
  · have hxH : x ∈ H := hRH (hUR hx)
    have hyH : y ∈ H := hRH hy.1
    have hxT : π ⟨x, hxH⟩ ∈ T := hUmap ▸ ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have hyW : π ⟨y, hyH⟩ ∈ W := ⟨⟨y, hyH⟩, Subgroup.mem_subgroupOf.mpr hy.2, rfl⟩
    have hc := hcomm _ hyW _ hxT
    have hN : x * y * x⁻¹ * y⁻¹ ∈ GLBPrimeCore p H := by
      refine (mem_glbPrimeCore_iff_mk_eq_one (⟨x, hxH⟩ * ⟨y, hyH⟩ * (⟨x, hxH⟩ : H)⁻¹ *
        (⟨y, hyH⟩ : H)⁻¹)).mpr ?_
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hπ, ← hc]
      group
    have hRc : x * y * x⁻¹ * y⁻¹ ∈ R :=
      R.mul_mem (R.mul_mem (R.mul_mem (hUR hx) hy.1) (R.inv_mem (hUR hx))) (R.inv_mem hy.1)
    have h1 : x * y * x⁻¹ * y⁻¹ = 1 := by
      have hmem : x * y * x⁻¹ * y⁻¹ ∈ R ⊓ GLBPrimeCore p H := ⟨hRc, hN⟩
      rwa [hRN, Subgroup.mem_bot] at hmem
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]

theorem D1OneLieData.unitary_u3Data (hK : KFactOneLie) (hKU2 : KFactUnitarySylowStructure)
    (hKU3 : KFactUnitarySylowCenterTorus) (hKU4 : KFactUnitaryTorusPPD)
    (hKU6 : KFactUnitaryBorelMaximal) (hKU8 : KFactUnitarySylowNormalizerSolvable)
    (hKU9 : KFactUnitaryAutElemRank) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1OneLieData p P M H R Rbar K) (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥)
    (hU : IsUnitaryGroup p K)
    (hZ : d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
      centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) :
    ∃ n : ℕ, D1OneLieU3Data p n P M H R (d1LiftX p H R K)
      (d1LiftX p H R (centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)))
      (d1PlusCore p H K) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hd.cfg.red.ne_two
  obtain ⟨d, hdU, hKe⟩ := hU
  have hKe' : Nonempty (K ≃* CatGroup d) := hKe
  obtain ⟨T₁, hT₁, hF⟩ := hd.oneLieFacts hK
  have hn2 : 2 ≤ d.1.fieldExponent := by
    by_contra hlt
    apply hd.big
    obtain ⟨E, -, hE, hEcard⟩ := pRank_attained p hp (⊤ : Subgroup (MulAut K))
    have h1 := hKU9 K p d hdU hKe' E hE
    rw [hEcard] at h1
    have h2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
    omega
  set n := d.1.fieldExponent with hn
  have hTF : OneLieTorusFacts p K T₁ n 1 :=
    oneLieTorusFacts_of_unitary hKU2 hKU3 hKU4 hKU6 hKU8 hKU9 hp2 hdU hn2 hKe' T₁
  obtain ⟨-, -, hperf, hrank⟩ := stmtOneLieBorel Rbar _ K n 1 hd.cfg.red hd.comp
    hd.noncyclic hd.z hd.center T₁ hT₁ hF hTF
  set Z := d1LiftX p H R
    (centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) with hZdef
  obtain ⟨hTcard, hTcomm, hTpow, -⟩ := hKU2 K p d hp2 hdU hKe' T₁
  obtain ⟨hZC, hcomm, hcardX, hpowX⟩ := hd.unitary_sylow hT₁ hTcard hTcomm hTpow
  obtain ⟨φ, -⟩ := hd.exists_torus_lift hT₁ hTF
  have hZcard : Nat.card Z = p ^ n := by
    rw [← Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd,
      GaloisField.card p n (by omega)]
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨r, hr, hrdvd, hprim⟩ :=
    CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one hp3
      (show 3 ≤ 2 * n by omega)
  have := Fact.mk hr
  obtain ⟨c, hcN, hcord, hcirr⟩ := hKU4 K p d hdU hn2 hKe' T₁ r hr hrdvd hprim
  have hpr : (p : ZMod r) ^ (2 * n) = 1 :=
    (CFSG.SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff hp.pos _).mp hrdvd
  have hord : orderOf (p : ZMod r) = 2 * n := by
    rw [orderOf_eq_iff (by omega)]
    exact ⟨hpr, fun k hk hk0 h => hprim k hk0 hk
      ((CFSG.SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff hp.pos k).mpr h)⟩
  have hp0 : (p : ZMod r) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hpr
    exact zero_ne_one hpr
  have hndvd : 2 * n ∣ r - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hp0
  have hr2n : 2 * n < r := by
    have h1 : 0 < r - 1 := by
      rcases Nat.lt_or_ge (r - 1) 1 with h | h
      · exfalso
        have : r = 2 := by have := hr.two_le; omega
        subst this
        obtain ⟨c', hc'⟩ := hndvd
        omega
      · omega
    have := Nat.le_of_dvd h1 hndvd
    omega
  have hrp : r ≠ p := by
    rintro rfl
    exact hp0 (ZMod.natCast_self r)
  have hrp1 : ¬ r ∣ p - 1 := by
    have h := hprim 1 one_pos (by omega)
    rwa [pow_one] at h
  obtain ⟨t, htK, htX, htr, htrX, htnt, hirr⟩ := hd.exists_lift_of_ppd hT₁ hcN hcord hcirr
  have htZ : t ∈ Subgroup.normalizer (Z : Set G) := by
    rw [hZdef, hZC]
    exact mem_normalizer_centerOf htX
  have htZc := mem_centralizer_of_isPGroup_of_card_eq_pow hZcard htZ htr
    (fun k hk hkn => hprim k hk (by omega)) hrp
  obtain ⟨hcnt1, hcirr1⟩ := hcirr 1 hr.not_dvd_one
  simp only [pow_one] at hcnt1 hcirr1
  obtain ⟨hZY, hXY, hXc⟩ := hd.unitary_pCore hK h84 hD2 hT₁ hF hcN hcnt1 hcirr1 hZ
  refine ⟨n, hd.toPhaseThree hK, hd.cfg.indBetaFour, hn2, d1LiftX_le p H R K, hZC, hcardX, hZcard,
    hcomm, hpowX, ?_, fun L hL hLL => ?_, fun A hAN hA => hd.isCyclic_of_le_d1PlusCore hAN hA,
    fun x hx c' hc' => ?_, ?_, hd.primeCore_inf_eq hK, hZY, hXY, hXc,
    ⟨r, t, hr, hr2n, hrp, hrp1, htK, htX, htr, htZc, htrX, htnt, hirr⟩⟩
  · have := pRank_inf_le_of_pRank_top_le (M := M) hp hrank
    simpa using this
  · exact le_d1PlusCore_of_map_le (hL.trans inf_le_left)
      (hperf _ (Subgroup.map_mono (Subgroup.subgroupOf_mono H hL))
        (commutator_map_eq_self (hL.trans inf_le_left) hLL))
  ·
    obtain ⟨x', ⟨-, hx'K⟩, rfl⟩ := hx
    obtain ⟨c'', hc''C, rfl⟩ := hc'
    have hcomm' := Subgroup.mem_centralizer_iff.mp hc''C _ (Subgroup.mem_comap.mp hx'K)
    refine (mem_glbPrimeCore_iff_mk_eq_one (x' * c'' * x'⁻¹ * c''⁻¹)).mpr ?_
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact hcomm'
  · exact (Subgroup.commutator_mono le_rfl (le_nclIn (d1LiftX_le_H p H R K))).trans
      (hd.commutator_nclIn_le hK h84 hD2 hY)

end PCore

end CFSG.AGLEmbedding
