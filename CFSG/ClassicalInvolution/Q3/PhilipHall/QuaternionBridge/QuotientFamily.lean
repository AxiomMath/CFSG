module

public import CFSG.ClassicalInvolution.Q3.TL3TwistQuot
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotGen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.Q8Twin

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {N : Subgroup Y} [N.Normal]

theorem core_inf_eq_bot (hd : TightDatum R S t) (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) :
    tightCore R ⊓ N = ⊥ :=
  eq_bot_iff.mpr ((inf_le_inf_right N (tightCore_le R)).trans (TwistQ.inf_eq_bot hd hN2 htN).le)

theorem inf_conj_eq_bot (hd : TightDatum R S t) (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N)
    {K : Subgroup Y} (hK : K ∈ CoreAssembly.conjClass (tightCore R)) : N ⊓ K = ⊥ := by
  obtain ⟨g, rfl⟩ := hK
  have h0 := core_inf_eq_bot hd hN2 htN
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxN, hxK⟩ := Subgroup.mem_inf.mp hx
  rw [mem_conjSub_iff] at hxK
  have hxN' : g⁻¹ * x * g ∈ N := by
    have h3 := (inferInstance : N.Normal).conj_mem _ hxN g⁻¹
    rwa [inv_inv] at h3
  have h1 : g⁻¹ * x * g ∈ tightCore R ⊓ N := ⟨hxK, hxN'⟩
  rw [h0, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem odd_inf_conj (hd : TightDatum R S t) (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N)
    {K : Subgroup Y} (hK : K ∈ CoreAssembly.conjClass (tightCore R)) :
    Odd (Nat.card ↥(N ⊓ K)) := by
  rw [inf_conj_eq_bot hd hN2 htN hK, Subgroup.card_bot]
  exact odd_one

theorem image_conjClass (A : Subgroup Y) :
    Set.image (fun K : Subgroup Y => K.map (QuotientGroup.mk' N)) (CoreAssembly.conjClass A) =
      CoreAssembly.conjClass (A.map (QuotientGroup.mk' N)) := by
  ext J
  constructor
  · rintro ⟨K, ⟨g, rfl⟩, rfl⟩
    exact ⟨QuotientGroup.mk' N g, (TwistQ.conjSub_map (N := N) g A).symm⟩
  · rintro ⟨gb, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gb
    exact ⟨conjSub g A, ⟨g, rfl⟩, TwistQ.conjSub_map (N := N) g A⟩

theorem hypOmegaGen_map (hd : TightDatum R S t) (hNc : N ≤ Subgroup.center Y)
    (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) :
    HypOmegaGen (CoreAssembly.conjClass ((tightCore R).map (QuotientGroup.mk' N))) := by
  rw [← image_conjClass (N := N)]
  exact CentQ.quotient_hypOmegaGen hd.hypOmegaGen N hNc fun K hK => odd_inf_conj hd hN2 htN hK

theorem isUniqueInvolution_map_core (hd : TightDatum R S t) (hN2 : IsPGroup 2 ↥N)
    (htN : t ∉ N) :
    IsUniqueInvolution ((tightCore R).map (QuotientGroup.mk' N)) (QuotientGroup.mk' N t) :=
  isUniqueInvolution_map_mk_of_odd
    (odd_inf_conj hd hN2 htN (CoreAssembly.mem_conjClass_self _)) hd.isUniqueInvolution_core

theorem q8TwinDatum_map (hd : TightDatum R S t) (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) :
    Q8TwinDatum (R.map (QuotientGroup.mk' N)) (TwistQ.sylowMap N S) (QuotientGroup.mk' N t) := by
  have hRN := TwistQ.inf_eq_bot hd hN2 htN
  have hcent : R.map (QuotientGroup.mk' N) ≤
      Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N)) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hd.cent hr)]
  refine ⟨?_, ?_, ?_, hcent, ?_⟩
  · obtain ⟨r, hr, ⟨e⟩⟩ := hd.quat
    exact ⟨r, hr, ⟨(TwistQ.sylowMapEquiv hRN S).symm.trans e⟩⟩
  · rw [TwistQ.sylowMap_map_subtype]
    exact Subgroup.mem_map_of_mem _ hd.mem
  · refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← hd.order, pow_orderOf_eq_one, map_one]
    · rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
      exact htN
  · have he := CFSG.ABGLocalTools.oddCore_map_mulEquiv (TwistQ.mapEquiv (N := N) hRN)
    exact hd.twoGroup.of_equiv (QuotientGroup.congr _ _ (TwistQ.mapEquiv hRN) he)

theorem tightCls_map (hd : TightDatum R S t) (hNc : N ≤ Subgroup.center Y)
    (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) (hc : TightCls Y R S t) :
    TightCls (Y ⧸ N) (R.map (QuotientGroup.mk' N)) (TwistQ.sylowMap N S)
      (QuotientGroup.mk' N t) :=
  TwistQ.cls hd hNc hN2 htN hc

theorem conjSub_map_ne_of_twin (hd : TightDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) (hNc : N ≤ Subgroup.center Y)
    (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) {c y : Y} (hcN : c ∈ N) (hc1 : c ≠ 1)
    (hy : y * t * y⁻¹ = t * c) :
    conjSub (QuotientGroup.mk' N y) ((tightCore R).map (QuotientGroup.mk' N)) ≠
      (tightCore R).map (QuotientGroup.mk' N) := by
  intro heq
  rw [← TwistQ.conjSub_map (N := N)] at heq
  have h0 := core_inf_eq_bot hd hN2 htN
  have htK : t ∈ tightCore R := hd.isUniqueInvolution_core.mem
  have hcZ : ∀ a : Y, a * c = c * a := Subgroup.mem_center_iff.mp (hNc hcN)
  have hS₀K : (S : Subgroup R).map R.subtype ≤ tightCore R := hd.sylow_core.1
  have hsq : ∀ k ∈ tightCore R, ∀ ν ∈ N, (k * ν) * (k * ν) = t * c → ν * ν = c := by
    intro k hk ν hν hkν
    have hνZ : ∀ a : Y, a * ν = ν * a := Subgroup.mem_center_iff.mp (hNc hν)
    have e1 : (k * ν) * (k * ν) = (k * k) * (ν * ν) := by
      calc (k * ν) * (k * ν) = k * (ν * k) * ν := by group
        _ = k * (k * ν) * ν := by rw [← hνZ k]
        _ = (k * k) * (ν * ν) := by group
    rw [e1] at hkν
    have h2 : t⁻¹ * (k * k) ∈ tightCore R ⊓ N := by
      refine ⟨(tightCore R).mul_mem ((tightCore R).inv_mem htK)
        ((tightCore R).mul_mem hk hk), ?_⟩
      have : t⁻¹ * (k * k) = c * (ν * ν)⁻¹ := by
        have h3 : k * k = t * c * (ν * ν)⁻¹ := by
          rw [← hkν]
          group
        rw [h3]
        have hcc : t⁻¹ * (t * c * (ν * ν)⁻¹) = c * (ν * ν)⁻¹ := by group
        exact hcc
      rw [this]
      exact N.mul_mem hcN (N.inv_mem (N.mul_mem hν hν))
    rw [h0, Subgroup.mem_bot] at h2
    have h3 : k * k = t := by
      calc k * k = t * (t⁻¹ * (k * k)) := by group
        _ = t := by rw [h2, mul_one]
    rw [h3] at hkν
    exact (mul_left_cancel hkν)
  have hdec : ∀ r ∈ tightCore R, ∃ k ∈ tightCore R, ∃ ν ∈ N, y * r * y⁻¹ = k * ν := by
    intro r hr
    have h1 : QuotientGroup.mk' N (y * r * y⁻¹) ∈
        (conjSub y (tightCore R)).map (QuotientGroup.mk' N) :=
      Subgroup.mem_map_of_mem _ (conj_mem_conjSub hr)
    rw [heq] at h1
    obtain ⟨k, hk, hkx⟩ := h1
    refine ⟨k, hk, k⁻¹ * (y * r * y⁻¹), ?_, by group⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkx
    exact hkx
  obtain ⟨r₁, hr₁, r₂, hr₂, h1, h2, h12⟩ := hd.exists_S₀_pair hq8
  have hr₁K := hS₀K hr₁
  have hr₂K := hS₀K hr₂
  obtain ⟨k₁, hk₁, ν₁, hν₁, e₁⟩ := hdec r₁ hr₁K
  obtain ⟨k₂, hk₂, ν₂, hν₂, e₂⟩ := hdec r₂ hr₂K
  have hsq₁ : y * r₁ * y⁻¹ * (y * r₁ * y⁻¹) = t * c := by
    calc y * r₁ * y⁻¹ * (y * r₁ * y⁻¹) = y * (r₁ * r₁) * y⁻¹ := by group
      _ = t * c := by rw [h1, hy]
  have hsq₂ : y * r₂ * y⁻¹ * (y * r₂ * y⁻¹) = t * c := by
    calc y * r₂ * y⁻¹ * (y * r₂ * y⁻¹) = y * (r₂ * r₂) * y⁻¹ := by group
      _ = t * c := by rw [h2, hy]
  have hsq₃ : y * (r₁ * r₂) * y⁻¹ * (y * (r₁ * r₂) * y⁻¹) = t * c := by
    calc y * (r₁ * r₂) * y⁻¹ * (y * (r₁ * r₂) * y⁻¹) = y * ((r₁ * r₂) * (r₁ * r₂)) * y⁻¹ := by
          group
      _ = t * c := by rw [h12, hy]
  rw [e₁] at hsq₁
  rw [e₂] at hsq₂
  have hν₁c := hsq k₁ hk₁ ν₁ hν₁ hsq₁
  have hν₂c := hsq k₂ hk₂ ν₂ hν₂ hsq₂
  have hx₃ : y * (r₁ * r₂) * y⁻¹ = (k₁ * k₂) * (ν₁ * ν₂) := by
    have e3 : y * (r₁ * r₂) * y⁻¹ = (y * r₁ * y⁻¹) * (y * r₂ * y⁻¹) := by group
    rw [e3, e₁, e₂]
    have hνZ : ∀ a : Y, a * ν₁ = ν₁ * a := Subgroup.mem_center_iff.mp (hNc hν₁)
    calc k₁ * ν₁ * (k₂ * ν₂) = k₁ * (ν₁ * k₂) * ν₂ := by group
      _ = k₁ * (k₂ * ν₁) * ν₂ := by rw [← hνZ k₂]
      _ = (k₁ * k₂) * (ν₁ * ν₂) := by group
  rw [hx₃] at hsq₃
  have hν₃c := hsq (k₁ * k₂) ((tightCore R).mul_mem hk₁ hk₂) (ν₁ * ν₂) (N.mul_mem hν₁ hν₂) hsq₃
  have hνZ₂ : ∀ a : Y, a * ν₁ = ν₁ * a := Subgroup.mem_center_iff.mp (hNc hν₁)
  have hcc : (ν₁ * ν₂) * (ν₁ * ν₂) = (ν₁ * ν₁) * (ν₂ * ν₂) := by
    calc (ν₁ * ν₂) * (ν₁ * ν₂) = ν₁ * (ν₂ * ν₁) * ν₂ := by group
      _ = ν₁ * (ν₁ * ν₂) * ν₂ := by rw [← hνZ₂ ν₂]
      _ = (ν₁ * ν₁) * (ν₂ * ν₂) := by group
  rw [hcc, hν₁c, hν₂c] at hν₃c
  exact hc1 (mul_left_cancel (a := c) (by rw [mul_one]; exact hν₃c))

theorem exists_twin_map (hd : TightDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) (hNc : N ≤ Subgroup.center Y)
    (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) {c y : Y} (hcN : c ∈ N) (hc1 : c ≠ 1)
    (hy : y * t * y⁻¹ = t * c) :
    ∃ K' ∈ twinSet (CoreAssembly.conjClass ((tightCore R).map (QuotientGroup.mk' N)))
      ((tightCore R).map (QuotientGroup.mk' N)),
      K' ≠ (tightCore R).map (QuotientGroup.mk' N) := by
  refine ⟨conjSub (QuotientGroup.mk' N y) ((tightCore R).map (QuotientGroup.mk' N)), ?_,
    conjSub_map_ne_of_twin hd hq8 hNc hN2 htN hcN hc1 hy⟩
  have hz := isUniqueInvolution_map_core hd hN2 htN
  have hfix : QuotientGroup.mk' N y * QuotientGroup.mk' N t * (QuotientGroup.mk' N y)⁻¹ =
      QuotientGroup.mk' N t := by
    have hπc : QuotientGroup.mk' N c = 1 := (QuotientGroup.eq_one_iff c).mpr hcN
    rw [← map_inv, ← map_mul, ← map_mul, hy, map_mul, hπc, mul_one]
  refine ⟨⟨QuotientGroup.mk' N y, ?_⟩, QuotientGroup.mk' N t, hz, ?_⟩
  · rfl
  · have := hz.conj (QuotientGroup.mk' N y)
    rwa [hfix] at this

structure Q8Quot (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (N : Subgroup Y) [N.Normal] : Prop where
  datum : Q8TwinDatum (R.map (QuotientGroup.mk' N)) (TwistQ.sylowMap N S) (QuotientGroup.mk' N t)
  cls : TightCls (Y ⧸ N) (R.map (QuotientGroup.mk' N)) (TwistQ.sylowMap N S)
    (QuotientGroup.mk' N t)
  hyp : HypOmegaGen (CoreAssembly.conjClass (tightCore (R.map (QuotientGroup.mk' N))))
  sylow : ∃ P : Subgroup (Y ⧸ N), IsSylow2In P (tightCore (R.map (QuotientGroup.mk' N))) ∧
    Nonempty (↥P ≃* QuaternionGroup 2)
  twin : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore (R.map (QuotientGroup.mk' N))))
    (tightCore (R.map (QuotientGroup.mk' N))), K' ≠ tightCore (R.map (QuotientGroup.mk' N))
  card_lt : Nat.card (Y ⧸ N) < Nat.card Y

theorem q8Quot_of_twin (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hNc : N ≤ Subgroup.center Y) (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) {c y : Y} (hcN : c ∈ N)
    (hc1 : c ≠ 1) (hy : y * t * y⁻¹ = t * c) : Q8Quot R S t N := by
  have hRN := TwistQ.inf_eq_bot hd hN2 htN
  have hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2) := hc.1
  have hcore : tightCore (R.map (QuotientGroup.mk' N)) = (tightCore R).map (QuotientGroup.mk' N) :=
    (TwistQ.tightCore_map hRN).symm
  refine ⟨q8TwinDatum_map hd hN2 htN, tightCls_map hd hNc hN2 htN hc, ?_, ?_, ?_, ?_⟩
  · rw [hcore]
    exact hypOmegaGen_map hd hNc hN2 htN
  ·
    rw [hcore]
    set S₀ : Subgroup Y := (S : Subgroup R).map R.subtype with hS₀
    have hS₀N : S₀ ⊓ N = ⊥ :=
      eq_bot_iff.mpr ((inf_le_inf_right N hd.S₀_le).trans hRN.le)
    refine ⟨S₀.map (QuotientGroup.mk' N),
      Hall196.isSylow2In_map_hom (QuotientGroup.mk' N) hd.sylow_core,
      ⟨((AscQuot.quotRestrictEquiv hS₀N).symm.trans
        (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm).trans
        hq8.some⟩⟩
  · rw [hcore]
    exact exists_twin_map hd hq8 hNc hN2 htN hcN hc1 hy
  · exact TwistQ.card_lt (N := N) (fun h => hc1 (by
      have := hcN
      rw [h, Subgroup.mem_bot] at this
      exact this))

end CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
