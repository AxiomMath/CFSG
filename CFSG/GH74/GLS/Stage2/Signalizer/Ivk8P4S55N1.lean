module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55HH
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55CentExt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Hyp89
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8K0Act

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74.GLS.Stage12 CFSG.ABGLocalTools
open scoped commutatorElement

@[expose] def N1Config (Y : Type) [Group Y] (p : ℕ) (b : MulAut Y) (R₀ : Subgroup Y) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ orderOf b = p ∧ IsSylowOf 2 R₀ ⊤ ∧
    IsPGroup p ↥(closure {c : MulAut Y | ∃ r ∈ R₀, c = MulAut.conj r * b * (MulAut.conj r)⁻¹})

@[expose] def HHObsAt (p r : ℕ) (Y : Type) [Group Y] (b : MulAut Y) : Prop :=
  r.Prime ∧ r ≠ p ∧ ∃ E : Subgroup Y, IsPGroup r ↥E ∧
    (r = 2 → ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, b x ∈ E) ∧ ∃ x ∈ E, b x ≠ x

@[expose] def HHObs (p : ℕ) (Y : Type) [Group Y] (b : MulAut Y) : Prop :=
  ∃ r : ℕ, HHObsAt p r Y b

@[expose] def NoR (r : ℕ) (Y : Type) [Group Y] : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → Nonempty ((K ⧸ center K) ≃* Y) →
    ¬ r ∣ Nat.card (center K)

@[expose] def MultAlt55 : Prop :=
  (∀ (K : Type) [Group K] [Finite K], IsQuasisimple K →
      Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin 7)) → Nat.card (center K) ∣ 6) ∧
    ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K →
      Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin 11)) → Nat.card (center K) ∣ 2

@[expose] def N1Fam (F : (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p : ℕ) (b : MulAut Y) (R₀ : Subgroup Y), F Y →
    N1Config Y p b R₀ →
    (p = 3 ∧ (Nonempty (Y ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (Y ≃* alternatingGroup (Fin 11))) ∧ HHObs p Y b) ∨
      ∃ r : ℕ, HHObsAt p r Y b ∧ (r = 2 → NoR 2 Y)

section Induced

variable {Γ : Type} [Group Γ]

theorem mem_normalizer_of_normal {K : Subgroup Γ} (hK : K.Normal) (a : Γ) :
    a ∈ normalizer (K : Set Γ) := by
  rw [Subgroup.normalizer_eq_top_iff.mpr hK]
  exact Subgroup.mem_top a

@[expose] noncomputable def bAut {K : Subgroup Γ} (hK : K.Normal) (a : Γ) :
    MulAut (↥K ⧸ center ↥K) :=
  YCfg.yAct K ⟨a, mem_normalizer_of_normal hK a⟩

theorem bAut_mk {K : Subgroup Γ} (hK : K.Normal) (a : Γ) (x : ↥K) :
    bAut hK a (QuotientGroup.mk x) =
      QuotientGroup.mk (⟨a * (x : Γ) * a⁻¹, hK.conj_mem _ x.2 a⟩ : ↥K) :=
  YCfg.yAct_apply_mk K ⟨a, mem_normalizer_of_normal hK a⟩ x

@[expose] noncomputable def bAutN (K : Subgroup Γ) (a : Γ) (ha : a ∈ normalizer (K : Set Γ)) :
    MulAut (↥K ⧸ center ↥K) :=
  YCfg.yAct K ⟨a, ha⟩

theorem bAutN_mk (K : Subgroup Γ) (a : Γ) (ha : a ∈ normalizer (K : Set Γ)) (x : ↥K)
    (hx : a * (x : Γ) * a⁻¹ ∈ K) :
    bAutN K a ha (QuotientGroup.mk x) = QuotientGroup.mk (⟨a * (x : Γ) * a⁻¹, hx⟩ : ↥K) :=
  YCfg.yAct_apply_mk K ⟨a, ha⟩ x

theorem bAutN_eq_yAct (K : Subgroup Γ) (a : Γ) (ha : a ∈ normalizer (K : Set Γ)) :
    bAutN K a ha = YCfg.yAct K ⟨a, ha⟩ := rfl

theorem bAutN_inv (K : Subgroup Γ) (a : Γ) (ha : a ∈ normalizer (K : Set Γ)) :
    bAutN K a⁻¹ ((normalizer (K : Set Γ)).inv_mem ha) = (bAutN K a ha)⁻¹ := by
  rw [bAutN, bAutN, ← map_inv]
  rfl

@[expose] noncomputable def Rbar (K R : Subgroup Γ) : Subgroup (↥K ⧸ center ↥K) :=
  ((R ⊓ K).subgroupOf K).map (QuotientGroup.mk' (center ↥K))

theorem mem_Rbar {K R : Subgroup Γ} {r : ↥K ⧸ center ↥K} :
    r ∈ Rbar K R ↔ ∃ y : ↥K, (y : Γ) ∈ R ∧ (QuotientGroup.mk y : ↥K ⧸ center ↥K) = r := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, (Subgroup.mem_inf.mp hy).1, rfl⟩
  · rintro ⟨y, hyR, rfl⟩
    exact ⟨y, Subgroup.mem_inf.mpr ⟨hyR, y.2⟩, rfl⟩

end Induced

section Reduction

variable {k : Kind} {p : ℕ} {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V]
  [Module (ZMod p) V] {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ} {K : Subgroup Γ} {a : Γ} {P R : Subgroup Γ}

theorem Frame55.n1 [Finite Γ] (hf : Frame55 k p ρ K a P R) :
    N1Config (↥K ⧸ center ↥K) p (bAut hf.normal a) (Rbar K R) := by
  have hfp := Fact.mk hf.prime
  have hKn := hf.normal
  have hperf : Group.IsPerfect ↥K := hf.quasi.1
  have haN : a ∈ normalizer (K : Set Γ) := mem_normalizer_of_normal hKn a
  have hpow : (⟨a, haN⟩ : ↥(normalizer (K : Set Γ))) ^ p = 1 :=
    Subtype.ext (by simpa using hf.toMod55.pow_prime)
  have hbp : bAut hKn a ^ p = 1 := by
    rw [bAut, ← map_pow, hpow, map_one]
  have hb1 : bAut hKn a ≠ 1 := by
    intro h1
    have hc : a ∈ centralizer (K : Set Γ) := (YCfg.yAct_eq_one_iff K ⟨a, haN⟩).mp h1
    apply hf.acts
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hcom : Commute a x := (Subgroup.mem_centralizer_iff.mp hc x hx).symm
    exact (hcom.zpow_left n).eq
  refine ⟨hf.prime, hf.odd, orderOf_eq_prime hbp hb1, ?_, ?_⟩
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨Q, hQ⟩ := hf.sylow.exists_sylow_eq_subgroupOf
    have hsurj : Function.Surjective (QuotientGroup.mk' (center ↥K)) :=
      QuotientGroup.mk'_surjective _
    have hQb : ((Q.mapSurjective hsurj : Sylow 2 (↥K ⧸ center ↥K)) : Subgroup _) =
        Rbar K R := by
      rw [Sylow.coe_mapSurjective, hQ]
      rfl
    rw [isSylowOf_iff]
    refine ⟨le_top, ?_, ?_⟩
    · rw [← hQb]
      exact (Q.mapSurjective hsurj).isPGroup'
    · rw [← hQb, Subgroup.relIndex_top_right]
      exact (Q.mapSurjective hsurj).not_dvd_index
  ·
    have hb : bAut hKn a ∈ K0.Pbar K P := K0.yAct_mem_Pbar haN hf.a_mem
    have hsub : closure {c : MulAut (↥K ⧸ center ↥K) | ∃ r ∈ Rbar K R,
        c = MulAut.conj r * bAut hKn a * (MulAut.conj r)⁻¹} ≤ K0.Pbar K P := by
      rw [Subgroup.closure_le]
      rintro c ⟨r, hr, rfl⟩
      obtain ⟨y, hyR, rfl⟩ := mem_Rbar.mp hr
      exact K0.conj_mem_Pbar (hf.norm hyR) hb
    exact IsPGroup.to_le (K0.isPGroup_Pbar hf.pgrp) hsub

theorem Hyp89.false_of_hhobsAt [Finite Γ] [Module.Finite (ZMod p) V]
    (hf : Hyp89 p ρ K a) {r : ℕ} (hZ : r = 2 → ¬ 2 ∣ Nat.card (center ↥K))
    (h : HHObsAt p r (↥K ⧸ center ↥K) (bAutN K a hf.norm)) : False := by
  obtain ⟨hr, hrp, E, hE, hab, hinv, x, hxE, hbx⟩ := h
  have haN' : a⁻¹ ∈ normalizer (K : Set Γ) := (normalizer (K : Set Γ)).inv_mem hf.norm
  have hcm : ∀ g ∈ normalizer (K : Set Γ), ∀ y : ↥K, g * (y : Γ) * g⁻¹ ∈ K :=
    fun g hg y => (Subgroup.mem_normalizer_iff.mp hg _).mp y.2
  have hfr : Fact r.Prime := ⟨hr⟩
  set π : ↥K →* (↥K ⧸ center ↥K) := QuotientGroup.mk' (center ↥K) with hπ
  have hpiy : ∀ y : ↥K, π y = QuotientGroup.mk y := fun y => rfl
  have hinv' : ∀ y ∈ E, (bAutN K a hf.norm)⁻¹ y ∈ E := by
    let f : ↥E → ↥E := fun z => ⟨bAutN K a hf.norm z, hinv z z.2⟩
    have hf_inj : Function.Injective f := fun z1 z2 h12 =>
      Subtype.ext ((bAutN K a hf.norm).injective (congrArg Subtype.val h12))
    have hf_surj := Finite.injective_iff_surjective.mp hf_inj
    intro y hy
    obtain ⟨z, hz⟩ := hf_surj ⟨y, hy⟩
    have hz' : bAutN K a hf.norm z = y := congrArg Subtype.val hz
    rw [← hz']
    simp
  have hnil : Group.IsNilpotent ↥(E.comap π) := by
    have hEn : Group.IsNilpotent ↥E := hE.isNilpotent
    refine Subgroup.isNilpotent_of_ker_le_center (π.subgroupComap E) ?_
    intro y hy
    have hy1 : π (y : ↥K) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
    have hyc : (y : ↥K) ∈ center ↥K := (QuotientGroup.eq_one_iff _).mp hy1
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hyc g.1)
  obtain ⟨Q, hQmax⟩ := exists_sylow_rmax_of_isNilpotent ↥(E.comap π) hr
  set SK : Subgroup ↥K := (Q : Subgroup ↥(E.comap π)).map (E.comap π).subtype with hSK
  have hSKmem : ∀ y : ↥K, y ∈ SK ↔
      ∃ hy : y ∈ E.comap π, (⟨y, hy⟩ : ↥(E.comap π)) ∈ (Q : Subgroup ↥(E.comap π)) := by
    intro y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, hw⟩
    · rintro ⟨hy, hyQ⟩
      exact ⟨⟨y, hy⟩, hyQ, rfl⟩
  have hSKp : IsPGroup r ↥SK := Q.isPGroup'.map (E.comap π).subtype
  have hSKle : ∀ y ∈ SK, π y ∈ E := fun y hy => ((hSKmem y).mp hy).1
  have hSKmax : ∀ y : ↥K, π y ∈ E → (∃ n : ℕ, y ^ r ^ n = 1) → y ∈ SK := by
    rintro y hyE ⟨n, hn⟩
    exact (hSKmem y).mpr ⟨hyE, hQmax ⟨y, hyE⟩ ⟨n, Subtype.ext (by simpa using hn)⟩⟩
  have hlift : ∃ k0 ∈ SK, π k0 = x := by
    have hsurj : Function.Surjective (π.subgroupComap E) :=
      MonoidHom.subgroupComap_surjective π E (QuotientGroup.mk'_surjective _)
    have htop := map_sylow_eq_top_of_isPGroup (π.subgroupComap E) hsurj hE Q
    have hxm : (⟨x, hxE⟩ : ↥E) ∈
        (Q : Subgroup ↥(E.comap π)).map (π.subgroupComap E) := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨w, hw, hwx⟩ := hxm
    exact ⟨(w : ↥K), (hSKmem _).mpr ⟨w.2, hw⟩, congrArg Subtype.val hwx⟩
  have hSKab : r = 2 → ∀ u ∈ SK, ∀ v ∈ SK, u * v = v * u := by
    intro hr2 u hu v hv
    have hrz : Nat.Coprime r (Nat.card (center ↥K)) := by
      rw [hr2]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (hZ hr2)
    have hπ12 : π (u * v) = π (v * u) := by
      rw [map_mul, map_mul]
      exact hab hr2 _ (hSKle u hu) _ (hSKle v hv)
    obtain ⟨w, hw⟩ : ∃ w : ↥K, w = (v * u)⁻¹ * (u * v) := ⟨_, rfl⟩
    have hwS : w ∈ SK := by
      rw [hw]
      exact SK.mul_mem (SK.inv_mem (SK.mul_mem hv hu)) (SK.mul_mem hu hv)
    have hwZ : w ∈ center ↥K := by
      rw [← QuotientGroup.eq_one_iff]
      have h1 : π w = 1 := by
        rw [hw, map_mul, map_inv, hπ12, inv_mul_cancel]
      exact h1
    obtain ⟨n, hn⟩ := hSKp ⟨w, hwS⟩
    have hwn : w ^ r ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hwz : w ^ Nat.card (center ↥K) = 1 := by
      have h2 := congrArg Subtype.val (pow_card_eq_one' (G := center ↥K) (x := ⟨w, hwZ⟩))
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
      exact h2
    have h3 : w = 1 := eq_one_of_pow_pow_of_pow hrz hwn hwz
    rw [hw] at h3
    exact (inv_mul_eq_one.mp h3).symm
  have hconj : ∀ g : Γ, ∀ hg : g ∈ normalizer (K : Set Γ),
      (∀ y : ↥K, π y ∈ E → π ⟨g * y * g⁻¹, hcm g hg y⟩ ∈ E) →
      ∀ y ∈ SK, (⟨g * y * g⁻¹, hcm g hg y⟩ : ↥K) ∈ SK := by
    intro g hg hgE y hy
    refine hSKmax _ (hgE y (hSKle y hy)) ?_
    obtain ⟨n, hn⟩ := hSKp ⟨y, hy⟩
    refine ⟨n, Subtype.ext ?_⟩
    have hyn : (y : Γ) ^ r ^ n = 1 := by
      simpa using congrArg (fun w : ↥SK => ((w : ↥K) : Γ)) hn
    change (g * (y : Γ) * g⁻¹) ^ r ^ n = 1
    rw [conj_pow, hyn]
    group
  have hSKa : ∀ y ∈ SK, (⟨a * y * a⁻¹, hcm a hf.norm y⟩ : ↥K) ∈ SK := by
    refine hconj a hf.norm (fun y hy => ?_)
    have h2 := hinv (QuotientGroup.mk y) hy
    rw [bAutN_mk K a hf.norm y (hcm a hf.norm y)] at h2
    exact h2
  have hSKa' : ∀ y ∈ SK, (⟨a⁻¹ * y * a⁻¹⁻¹, hcm a⁻¹ haN' y⟩ : ↥K) ∈ SK := by
    refine hconj a⁻¹ haN' (fun y hy => ?_)
    have h2 := hinv' (QuotientGroup.mk y) hy
    rw [← bAutN_inv K a hf.norm, bAutN_mk K a⁻¹ haN' y (hcm a⁻¹ haN' y)] at h2
    exact h2
  set S : Subgroup Γ := SK.map K.subtype with hS
  have hSp : IsPGroup r ↥S := hSKp.map K.subtype
  have haS : a ∈ normalizer (S : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_, hSKa y hy, rfl⟩
    · rintro ⟨y', hy', hyg⟩
      have hyg2 : (y' : Γ) = a * g * a⁻¹ := hyg
      have hgK : g ∈ K := by
        have hg' : g = a⁻¹ * (y' : Γ) * a⁻¹⁻¹ := by
          rw [hyg2]
          group
        rw [hg']
        exact hcm a⁻¹ haN' y'
      refine ⟨⟨g, hgK⟩, ?_, rfl⟩
      have h2 := hSKa' y' hy'
      have hyg' : (⟨a⁻¹ * (y' : Γ) * a⁻¹⁻¹, hcm a⁻¹ haN' y'⟩ : ↥K) = ⟨g, hgK⟩ := by
        apply Subtype.ext
        change a⁻¹ * (y' : Γ) * a⁻¹⁻¹ = g
        rw [hyg2]
        group
      rw [hyg'] at h2
      exact h2
  have hcent : S ≤ centralizer ({a} : Set Γ) := by
    by_cases hr2 : r = 2
    · have hSp2 : IsPGroup 2 ↥S := by
        rw [hr2] at hSp
        exact hSp
      refine hf.centralizes_abelian hSp2 ?_ haS
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      exact congrArg Subtype.val (hSKab hr2 u hu v hv)
    · exact hf.centralizes_odd hr hr2 hrp hSp haS
  obtain ⟨k0, hk0S, hk0x⟩ := hlift
  have hk0 : (k0 : Γ) ∈ S := ⟨k0, hk0S, rfl⟩
  have hcomm : a * (k0 : Γ) = (k0 : Γ) * a :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hcent hk0)).symm
  apply hbx
  rw [← hk0x, hpiy, bAutN_mk K a hf.norm k0 (hcm a hf.norm k0)]
  congr 1
  apply Subtype.ext
  change a * (k0 : Γ) * a⁻¹ = (k0 : Γ)
  rw [hcomm]
  group

theorem Mod55.false_of_hhobsAt [Finite Γ] [Module.Finite (ZMod p) V]
    (hf : Mod55 p ρ K a P) {r : ℕ} (hZ : r = 2 → ¬ 2 ∣ Nat.card (center ↥K))
    (h : HHObsAt p r (↥K ⧸ center ↥K) (bAut hf.normal a)) : False :=
  hf.toHyp89.false_of_hhobsAt hZ h

end Reduction

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
