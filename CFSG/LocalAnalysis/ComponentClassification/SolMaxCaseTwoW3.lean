module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCaseTwoW2
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCaseTwoEnd
public import CFSG.Holt.General.Aschbacher73
public import CFSG.Goldschmidt.Steps.GoldTypeBender
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv MulAction CFSG.Open
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter
  sylowCenter_le benderBorel_sylowCenter isStronglyEmbedded_of_fusion)
open CFSG.ComponentClassification.AschbacherToolkit.Goldschmidt (mem_sylowCenter_of_sq_eq_one)
open scoped MatrixGroups

namespace CaseTwoW

variable {X : Type} [Group X]

abbrev Cos (H : Subgroup X) (w : X) : Type :=
  ↥(centralizer ({w} : Set X)) ⧸ H.subgroupOf (centralizer ({w} : Set X))

abbrev permGrp (H : Subgroup X) (w : X) : Subgroup (Perm (Cos H w)) :=
  (toPermHom ↥(centralizer ({w} : Set X)) (Cos H w)).range

abbrev toPermGrp (H : Subgroup X) (w : X) :
    ↥(centralizer ({w} : Set X)) →* ↥(permGrp H w) :=
  (toPermHom ↥(centralizer ({w} : Set X)) (Cos H w)).rangeRestrict

abbrev basePt (H : Subgroup X) (w : X) : Cos H w := QuotientGroup.mk 1

abbrev wC (w : X) : ↥(centralizer ({w} : Set X)) := ⟨w, mem_centralizer_singleton_iff.mpr rfl⟩

variable {H : Subgroup X} {w : X}

theorem toPermGrp_smul (c : ↥(centralizer ({w} : Set X))) (ω : Cos H w) :
    toPermGrp H w c • ω = c • ω := rfl

theorem toPermGrp_surjective : Function.Surjective (toPermGrp H w) :=
  MonoidHom.rangeRestrict_surjective _

instance : IsPretransitive ↥(permGrp H w) (Cos H w) :=
  ⟨fun a b => by
    obtain ⟨c, hc⟩ := exists_smul_eq ↥(centralizer ({w} : Set X)) a b
    exact ⟨toPermGrp H w c, hc⟩⟩

theorem smul_mk_eq_iff (c d : ↥(centralizer ({w} : Set X))) :
    toPermGrp H w c • (QuotientGroup.mk d : Cos H w) = QuotientGroup.mk d ↔
      (d : X)⁻¹ * c * d ∈ H := by
  rw [toPermGrp_smul, MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul, mem_subgroupOf,
    ← H.inv_mem_iff]
  simp [mul_assoc]

theorem toPermGrp_mem_stabilizer_iff (c : ↥(centralizer ({w} : Set X))) :
    toPermGrp H w c ∈ stabilizer ↥(permGrp H w) (basePt H w) ↔ (c : X) ∈ H := by
  rw [mem_stabilizer_iff, basePt, smul_mk_eq_iff]
  simp

theorem toPermGrp_eq_one_iff (c : ↥(centralizer ({w} : Set X))) :
    toPermGrp H w c = 1 ↔ (c : X) ∈ coreSubgroup H w := by
  constructor
  · intro h
    refine ⟨mem_centralizer_singleton_iff.mp c.2, fun d hd => ?_⟩
    exact (smul_mk_eq_iff (H := H) c ⟨d, mem_centralizer_singleton_iff.mpr hd⟩).mp
      (by rw [h, one_smul])
  · intro h
    refine eq_of_smul_eq_smul (α := Cos H w) fun ω => ?_
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective ω
    rw [one_smul]
    exact (smul_mk_eq_iff c d).mpr (h.2 d (mem_centralizer_singleton_iff.mp d.2))

theorem mem_coreSubgroup_self (hwH : w ∈ H) : w ∈ coreSubgroup H w :=
  ⟨rfl, fun c hc => by rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]; exact hwH⟩

theorem toPermGrp_wC (hwH : w ∈ H) : toPermGrp H w (wC w) = 1 :=
  (toPermGrp_eq_one_iff _).mpr (mem_coreSubgroup_self hwH)

theorem exists_lift_of_mem_normalizer {L : Subgroup ↥(permGrp H w)} {Syl : Sylow 2 ↥L}
    (hSyl : (stabilizer ↥(permGrp H w) (basePt H w)).subgroupOf L =
      normalizer ((Syl : Subgroup ↥L) : Set ↥L)) {n : ↥L}
    (hn : n ∈ normalizer ((Syl : Subgroup ↥L) : Set ↥L)) :
    ∃ d : ↥(centralizer ({w} : Set X)), (d : X) ∈ H ∧ toPermGrp H w d = n := by
  rw [← hSyl, mem_subgroupOf] at hn
  obtain ⟨d, hd⟩ := toPermGrp_surjective (n : ↥(permGrp H w))
  exact ⟨d, (toPermGrp_mem_stabilizer_iff d).mp (hd ▸ hn), hd⟩

theorem eq_one_of_odd_of_isPGroup {K : Type*} [Group K] {Y : Subgroup K} (hY : IsPGroup 2 Y)
    {g : K} (hg : g ∈ Y) (hodd : Odd (orderOf g)) : g = 1 := by
  obtain ⟨k, hk⟩ := hY ⟨g, hg⟩
  have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  rcases j with _ | j
  · rwa [pow_zero, orderOf_eq_one_iff] at hj
  · rw [hj, pow_succ] at hodd
    exact absurd hodd (by simp [Nat.odd_mul, Nat.not_odd_iff_even])

theorem commute_inv_mul_of_conj {K : Type*} [Group K] {a b x e : K}
    (ha : a * x * a⁻¹ * x⁻¹ = 1 ∨ a * x * a⁻¹ * x⁻¹ = e)
    (hb : b * x * b⁻¹ * x⁻¹ = 1 ∨ b * x * b⁻¹ * x⁻¹ = e) (hab : a * x = x * a ↔ b * x = x * b) :
    a⁻¹ * b * x = x * (a⁻¹ * b) := by
  have key : ∀ g : K, g * x * g⁻¹ * x⁻¹ = 1 ↔ g * x = x * g := fun g => by
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  by_cases h : a * x = x * a
  · have h' := hab.mp h
    calc a⁻¹ * b * x = a⁻¹ * (b * x) := by group
      _ = a⁻¹ * (x * b) := by rw [h']
      _ = a⁻¹ * (x * a) * a⁻¹ * b := by group
      _ = a⁻¹ * (a * x) * a⁻¹ * b := by rw [h]
      _ = x * (a⁻¹ * b) := by group
  · have h' : ¬ b * x = x * b := fun hb' => h (hab.mpr hb')
    have ea : a * x * a⁻¹ * x⁻¹ = e := ha.resolve_left fun h1 => h ((key a).mp h1)
    have eb : b * x * b⁻¹ * x⁻¹ = e := hb.resolve_left fun h1 => h' ((key b).mp h1)
    have hab' : a * x * a⁻¹ = b * x * b⁻¹ := mul_right_cancel (ea.trans eb.symm)
    calc a⁻¹ * b * x = a⁻¹ * (b * x * b⁻¹) * b := by group
      _ = a⁻¹ * (a * x * a⁻¹) * b := by rw [hab']
      _ = x * (a⁻¹ * b) := by group

theorem p1_pt8 {m : ℕ} (hm : 13 ≤ m) : p1 hm (pt hm 8) = pt hm 9 := by
  rw [p1, pt, ι_apply_castLE]
  rfl

variable {M : Subgroup X} {m : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin m)} {t : X}

namespace Setup

variable (S : Setup H M θ ρ t w)
include S

theorem odd_orderOf_toPermGrp [Finite X] {c : ↥(centralizer ({w} : Set X))} (hcH : (c : X) ∈ H)
    (h1 : ρ ⟨c, S.HN hcH⟩ = 1) : Odd (orderOf (toPermGrp H w c)) := by
  have h := S.ker _ hcH (S.perm.mem_coreActionKernel _ h1)
  rw [orderOf_coe] at h
  exact Odd.of_dvd_nat h (orderOf_map_dvd _ c)

theorem smul_eq_iff_of_four [Finite X] {c : ↥(centralizer ({w} : Set X))} (hcH : (c : X) ∈ H)
    (hc2 : c * c = 1) (hc4 : (ρ ⟨c, S.HN hcH⟩).support.card = 4) (ω : Cos H w) :
    toPermGrp H w c • ω = ω ↔ ω = basePt H w := by
  have hc2' : (c : X) * c = 1 := congrArg Subtype.val hc2
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective ω
  rw [smul_mk_eq_iff, basePt, QuotientGroup.eq, mem_subgroupOf]
  constructor
  · intro h
    have hd := S.mem_of_conj_mem_of_four hcH hc2' hc4 h
    simpa using hd
  · intro h
    have hd : (d : X) ∈ H := by simpa using h
    exact mul_mem (mul_mem (inv_mem hd) hcH) hd

abbrev baseCent : Subgroup X :=
  wGroup S.m13 ρ (H ⊓ centralizer ({w} : Set X)) (inf_le_left.trans S.HN)

abbrev Qgrp : Subgroup ↥(permGrp H w) :=
  (S.baseCent.subgroupOf (centralizer ({w} : Set X))).map (toPermGrp H w)

theorem Q_fix [Finite X] {q : ↥(permGrp H w)} (hq : q ∈ S.Qgrp) (hq2 : orderOf q = 2)
    (ω : Cos H w) : q • ω = ω ↔ ω = basePt H w := by
  obtain ⟨c, hc, rfl⟩ := hq
  obtain ⟨hcHC, hcb⟩ := mem_subgroupOf.mp hc
  have hcH : (c : X) ∈ H := hcHC.1
  obtain ⟨hb, hbA⟩ := mem_baseSubgroup.mp hcb
  have h1 : ρ ⟨c, S.HN hcH⟩ ≠ 1 := fun h => by
    have := S.odd_orderOf_toPermGrp hcH h
    rw [hq2] at this
    exact absurd this (by decide)
  have h8 : ρ ⟨c, S.HN hcH⟩ ≠ σ8 S.m13 := fun h => by
    have hcwH : ((c * wC w : ↥(centralizer ({w} : Set X))) : X) ∈ H := mul_mem hcH S.wH
    have hρ1 : ρ ⟨((c * wC w : ↥(centralizer ({w} : Set X))) : X), S.HN hcwH⟩ = 1 := by
      have e := S.ρ_mul hcH S.wH
      rw [h, S.wσ, σ8_mul_self] at e
      exact e
    have := S.odd_orderOf_toPermGrp hcwH hρ1
    rw [map_mul, toPermGrp_wC S.wH, mul_one, hq2] at this
    exact absurd this (by decide)
  have h4 := card_support_eq_four_of_isBase hb hbA h1 h8
  obtain ⟨k, hk, hk2, hkρ⟩ := S.perm.exists_pow_involution S.HN S.ker hcH hb.mul_self
  have hψ : toPermGrp H w (c ^ k) = toPermGrp H w c := by
    obtain ⟨j, rfl⟩ := hk
    have hsq : toPermGrp H w c ^ 2 = 1 := by rw [← hq2]; exact pow_orderOf_eq_one _
    rw [map_pow, pow_succ, pow_mul, hsq, one_pow, one_mul]
  have hk4 : (ρ ⟨((c ^ k : ↥(centralizer ({w} : Set X))) : X),
      S.HN (pow_mem hcH k)⟩).support.card = 4 := by
    have e : ρ ⟨((c ^ k : ↥(centralizer ({w} : Set X))) : X), S.HN (pow_mem hcH k)⟩ =
        ρ ⟨c, S.HN hcH⟩ := hkρ
    rw [e]
    exact h4
  rw [← hψ]
  exact S.smul_eq_iff_of_four (c := c ^ k) (pow_mem hcH k) (Subtype.ext hk2) hk4 ω

theorem conj_mem_Q {d : ↥(centralizer ({w} : Set X))} (hdH : (d : X) ∈ H)
    {q : ↥(permGrp H w)} (hq : q ∈ S.Qgrp) :
    toPermGrp H w d * q * (toPermGrp H w d)⁻¹ ∈ S.Qgrp := by
  obtain ⟨c, hc, rfl⟩ := hq
  obtain ⟨hcHC, hcb⟩ := mem_subgroupOf.mp hc
  have hcH : (c : X) ∈ H := hcHC.1
  obtain ⟨hb, hbA⟩ := mem_baseSubgroup.mp hcb
  have hdcH : (d : X) * c * (d : X)⁻¹ ∈ H := mul_mem (mul_mem hdH hcH) (inv_mem hdH)
  have e : ρ ⟨(d : X) * c * (d : X)⁻¹, S.HN hdcH⟩ =
      ρ ⟨d, S.HN hdH⟩ * ρ ⟨c, S.HN hcH⟩ * (ρ ⟨d, S.HN hdH⟩)⁻¹ := by
    rw [S.ρ_mul (mul_mem hdH hcH) (inv_mem hdH), S.ρ_mul hdH hcH, S.ρ_inv hdH]
  refine ⟨d * c * d⁻¹, mem_subgroupOf.mpr ⟨⟨hdcH, (d * c * d⁻¹).2⟩, ?_⟩, by
    rw [map_mul, map_mul, map_inv]⟩
  show ρ ⟨(d : X) * c * (d : X)⁻¹, _⟩ ∈ baseSubgroup S.m13
  rw [e]
  exact ⟨isBase_conj (S.ρ_commute_σ8 hdH (mem_centralizer_singleton_iff.mp d.2)) hb,
    (alternatingGroup.normal (α := Fin m)).conj_mem _ hbA _⟩

theorem stabilizer_le_normalizer_Q :
    stabilizer ↥(permGrp H w) (basePt H w) ≤ normalizer (S.Qgrp : Set ↥(permGrp H w)) := by
  intro g hg
  obtain ⟨d, rfl⟩ := toPermGrp_surjective g
  have hdH : (d : X) ∈ H := (toPermGrp_mem_stabilizer_iff d).mp hg
  rw [mem_normalizer_iff]
  intro q
  refine ⟨S.conj_mem_Q hdH, fun hq => ?_⟩
  convert S.conj_mem_Q (d := d⁻¹) (inv_mem hdH) hq using 1
  rw [map_inv, inv_inv]
  group

theorem exists_inv_lift_comm₂ [Finite X] {b : Perm (Fin m)} (hbA : b ∈ alternatingGroup (Fin m))
    (hb : b * σ8 S.m13 = σ8 S.m13 * b) (hb2 : b * b = 1) {x x' : X} (hxH : x ∈ H)
    (hx'H : x' ∈ H) (hxw : x * w = w * x) (hx'w : x' * w = w * x') (hxx' : x' * x = x * x')
    (hx2 : x * x = 1) (hx'2 : x' * x' = 1) (hbx : b * ρ ⟨x, S.HN hxH⟩ = ρ ⟨x, S.HN hxH⟩ * b)
    (hbx' : b * ρ ⟨x', S.HN hx'H⟩ = ρ ⟨x', S.HN hx'H⟩ * b) :
    ∃ (y : X) (hy : y ∈ H), y * w = w * y ∧ y * x = x * y ∧ y * x' = x' * y ∧ y * y = 1 ∧
      ρ ⟨y, S.HN hy⟩ = b := by
  obtain ⟨y₀, hy₀M, hy₀w, hy₀⟩ := S.exists_lift hbA hb
  have hy₀H : y₀ ∈ H := S.MH hy₀M
  let A₁ : Subgroup X := H ⊓ centralizer ({w} : Set X)
  have hA₁H : A₁ ≤ H := inf_le_left
  have hxA₁ : x ∈ A₁ := ⟨hxH, mem_centralizer_singleton_iff.mpr hxw⟩
  have hy₀A₁ : y₀ ∈ A₁ := ⟨hy₀H, mem_centralizer_singleton_iff.mpr hy₀w⟩
  have hy₀' : ρ ⟨y₀, S.HN (hA₁H hy₀A₁)⟩ = b := hy₀
  obtain ⟨y₁, hy₁A₁, hy₁x, hy₁⟩ := S.perm.exists_commute_lift S.HN S.ker hA₁H hxA₁ hx2 hy₀A₁
    (by rw [hy₀']; exact hbx)
  rw [hy₀'] at hy₁
  let A₂ : Subgroup X := H ⊓ centralizer ({w} : Set X) ⊓ centralizer ({x} : Set X)
  have hA₂H : A₂ ≤ H := inf_le_left.trans inf_le_left
  have hx'A₂ : x' ∈ A₂ :=
    ⟨⟨hx'H, mem_centralizer_singleton_iff.mpr hx'w⟩, mem_centralizer_singleton_iff.mpr hxx'⟩
  have hy₁A₂ : y₁ ∈ A₂ := ⟨hy₁A₁, mem_centralizer_singleton_iff.mpr hy₁x⟩
  have hy₁' : ρ ⟨y₁, S.HN (hA₂H hy₁A₂)⟩ = b := hy₁
  obtain ⟨y₂, hy₂A₂, hy₂x', hy₂⟩ := S.perm.exists_commute_lift S.HN S.ker hA₂H hx'A₂ hx'2 hy₁A₂
    (by rw [hy₁']; exact hbx')
  rw [hy₁'] at hy₂
  have hy₂H : y₂ ∈ H := hA₂H hy₂A₂
  have hy₂w : y₂ * w = w * y₂ := mem_centralizer_singleton_iff.mp hy₂A₂.1.2
  have hy₂x : y₂ * x = x * y₂ := mem_centralizer_singleton_iff.mp hy₂A₂.2
  obtain ⟨k, -, hk2, hk⟩ := S.perm.exists_pow_involution S.HN S.ker hy₂H (by rw [hy₂]; exact hb2)
  exact ⟨y₂ ^ k, pow_mem hy₂H k, (Commute.pow_left hy₂w k).eq, (Commute.pow_left hy₂x k).eq,
    (Commute.pow_left hy₂x' k).eq, hk2, hk.trans hy₂⟩

structure Config (x₁ x₂ c p : ↥(centralizer ({w} : Set X))) : Prop where
  h₁ : (x₁ : X) ∈ H
  h₂ : (x₂ : X) ∈ H
  hc : (c : X) ∈ H
  hp : (p : X) ∈ H
  sq₁ : x₁ * x₁ = 1
  sq₂ : x₂ * x₂ = 1
  sqp : p * p = 1
  c₁₂ : x₁ * x₂ = x₂ * x₁
  cp₁ : p * x₁ = x₁ * p
  cp₂ : p * x₂ = x₂ * p
  conj : c * x₁ * c⁻¹ = x₂
  ρ₁ : ρ ⟨x₁, S.HN h₁⟩ = b1 S.m13
  ρ₂ : ρ ⟨x₂, S.HN h₂⟩ = b2 S.m13
  ρp : ρ ⟨p, S.HN hp⟩ = p1 S.m13

theorem exists_config [Finite X] : ∃ x₁ x₂ c p, S.Config x₁ x₂ c p := by
  obtain ⟨y₁, hy₁H, hy₁w, hy₁2, hy₁ρ⟩ :=
    S.exists_inv_lift (b1_mem S.m13) (σ8_b1 S.m13).symm (b1_mul_self S.m13)
  obtain ⟨y₂, hy₂H, hy₂w, hy₂1, hy₂2, hy₂ρ⟩ :=
    S.exists_inv_lift_comm (b2_mem S.m13) (σ8_b2 S.m13).symm (b2_mul_self S.m13) hy₁H hy₁w hy₁2
      (by rw [hy₁ρ]; exact (b1_b2 S.m13).symm)
  obtain ⟨y, hyH, hyw, hyc⟩ := S.exists_conj_lift hy₁H hy₂H hy₁w hy₂w hy₁2 hy₂2 (c12_mem S.m13)
    (σ8_c12 S.m13).symm (by rw [hy₁ρ, hy₂ρ]; exact c12_conj_b1 S.m13)
  obtain ⟨q, hqH, hqw, hq1, hq2, hqq, hqρ⟩ :=
    S.exists_inv_lift_comm₂ (p1_mem S.m13) (σ8_p1 S.m13).symm (p1_mul_self S.m13) hy₁H hy₂H hy₁w
      hy₂w hy₂1 hy₁2 hy₂2 (by rw [hy₁ρ]; exact (b1_p1 S.m13).symm)
      (by rw [hy₂ρ]; exact (b2_p1 S.m13).symm)
  exact ⟨⟨y₁, mem_centralizer_singleton_iff.mpr hy₁w⟩, ⟨y₂, mem_centralizer_singleton_iff.mpr hy₂w⟩,
    ⟨y, mem_centralizer_singleton_iff.mpr hyw⟩, ⟨q, mem_centralizer_singleton_iff.mpr hqw⟩,
    ⟨hy₁H, hy₂H, hyH, hqH, Subtype.ext hy₁2, Subtype.ext hy₂2, Subtype.ext hqq,
      Subtype.ext hy₂1.symm, Subtype.ext hq1, Subtype.ext hq2, Subtype.ext hyc, hy₁ρ, hy₂ρ, hqρ⟩⟩

namespace Config

variable {S} {x₁ x₂ c p : ↥(centralizer ({w} : Set X))} (cfg : S.Config x₁ x₂ c p)
include cfg

theorem h₁₂ : ((x₁ * x₂ : ↥(centralizer ({w} : Set X))) : X) ∈ H := mul_mem cfg.h₁ cfg.h₂

theorem sq₁₂ : x₁ * x₂ * (x₁ * x₂) = 1 := by
  calc x₁ * x₂ * (x₁ * x₂) = x₁ * (x₂ * x₁) * x₂ := by group
    _ = x₁ * (x₁ * x₂) * x₂ := by rw [cfg.c₁₂]
    _ = 1 := by rw [← mul_assoc, cfg.sq₁, one_mul, cfg.sq₂]

theorem four₁ : (ρ ⟨x₁, S.HN cfg.h₁⟩).support.card = 4 := by
  rw [cfg.ρ₁]; exact card_support_b1 S.m13

theorem four₂ : (ρ ⟨x₂, S.HN cfg.h₂⟩).support.card = 4 := by
  rw [cfg.ρ₂]; exact card_support_b2 S.m13

theorem ρ₁₂ : ρ ⟨((x₁ * x₂ : ↥(centralizer ({w} : Set X))) : X), S.HN cfg.h₁₂⟩ =
    b1 S.m13 * b2 S.m13 := by
  have e := S.ρ_mul cfg.h₁ cfg.h₂
  rw [cfg.ρ₁, cfg.ρ₂] at e
  exact e

theorem four₁₂ : (ρ ⟨((x₁ * x₂ : ↥(centralizer ({w} : Set X))) : X),
    S.HN cfg.h₁₂⟩).support.card = 4 := by
  rw [cfg.ρ₁₂]; exact card_support_b1b2 S.m13

end Config

theorem exists_sylow [Finite X] {x₁ x₂ c p : ↥(centralizer ({w} : Set X))}
    (cfg : S.Config x₁ x₂ c p) :
    ∃ P : Sylow 2 ↥(centralizer ({w} : Set X)), wC w ∈ P ∧ x₁ ∈ P ∧ x₂ ∈ P := by
  classical
  let k : Set ↥(centralizer ({w} : Set X)) := {wC w, x₁, x₂}
  have hw1 : Commute (wC w) x₁ := Subtype.ext (mem_centralizer_singleton_iff.mp x₁.2).symm
  have hw2 : Commute (wC w) x₂ := Subtype.ext (mem_centralizer_singleton_iff.mp x₂.2).symm
  have h12 : Commute x₁ x₂ := cfg.c₁₂
  have hcomm : k.Pairwise Commute := by
    intro a ha b hb _
    simp only [k, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals first
      | exact Commute.refl _
      | exact hw1 | exact hw2 | exact h12 | exact hw1.symm | exact hw2.symm | exact h12.symm
  have hab := isMulCommutative_closure hcomm
  have hgen : ∀ a ∈ k, a * a = 1 := by
    intro a ha
    simp only [k, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact Subtype.ext S.w2
    · exact cfg.sq₁
    · exact cfg.sq₂
  have hsq : ∀ y ∈ closure k, y * y = 1 := by
    intro y hy
    induction hy using closure_induction with
    | mem a ha => exact hgen a ha
    | one => exact mul_one 1
    | mul a b ha hb iha ihb =>
      have hab' : a * b = b * a := congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab']
        _ = 1 := by rw [← mul_assoc, iha, one_mul, ihb]
    | inv a ha iha =>
      calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        _ = 1 := by rw [iha, inv_one]
  have hP : IsPGroup 2 (closure k) := fun y =>
    ⟨1, Subtype.ext (by rw [pow_one, sq]; exact hsq y y.2)⟩
  obtain ⟨P, hP⟩ := hP.exists_le_sylow
  exact ⟨P, hP (subset_closure (by simp [k])), hP (subset_closure (by simp [k])),
    hP (subset_closure (by simp [k]))⟩

theorem exists_base_of_involution [Finite X] (hc₀ : ∃ c₀ : X, c₀ * w = w * c₀ ∧ c₀ ∉ H)
    {x₁ x₂ c p : ↥(centralizer ({w} : Set X))} (cfg : S.Config x₁ x₂ c p)
    {L : Subgroup ↥(permGrp H w)} {Syl : Sylow 2 ↥L}
    (hSyl : (stabilizer ↥(permGrp H w) (basePt H w)).subgroupOf L =
      normalizer ((Syl : Subgroup ↥L) : Set ↥L))
    (hSE : fusionStronglyEmbedded (normalizer ((Syl : Subgroup ↥L) : Set ↥L)))
    (hx₁L : toPermGrp H w x₁ ∈ L) {s : ↥L} (hs : s ∈ normalizer ((Syl : Subgroup ↥L) : Set ↥L))
    (hs1 : s ≠ 1) (hs2 : s ^ 2 = 1) :
    ∃ (y : ↥(centralizer ({w} : Set X))) (hy : (y : X) ∈ H), y * y = 1 ∧
      (ρ ⟨y, S.HN hy⟩).support.card = 4 ∧ ρ ⟨y, S.HN hy⟩ ∈ baseSubgroup S.m13 ∧
      toPermGrp H w y = s := by
  have hx₁2 : (x₁ : X) * x₁ = 1 := congrArg Subtype.val cfg.sq₁
  let z : ↥L := ⟨toPermGrp H w x₁, hx₁L⟩
  have hzN : z ∈ normalizer ((Syl : Subgroup ↥L) : Set ↥L) := by
    rw [← hSyl, mem_subgroupOf]
    exact (toPermGrp_mem_stabilizer_iff x₁).mpr cfg.h₁
  have hz1 : z ≠ 1 := fun h => S.not_mem_coreSubgroup_of_four hc₀ cfg.h₁ hx₁2 cfg.four₁
    ((toPermGrp_eq_one_iff x₁).mp (congrArg Subtype.val h))
  have hz2 : z ^ 2 = 1 := Subtype.ext (by
    change toPermGrp H w x₁ ^ 2 = 1
    rw [sq, ← map_mul, cfg.sq₁, map_one])
  obtain ⟨n, hn, hns⟩ := (isStronglyEmbedded_of_fusion hSE).involutions_conjugate_in hzN
    ⟨hz1, hz2⟩ hs ⟨hs1, hs2⟩
  obtain ⟨d, hdH, hd⟩ := exists_lift_of_mem_normalizer hSyl hn
  have hdw : (d : X) * w = w * d := mem_centralizer_singleton_iff.mp d.2
  have hyH : ((d⁻¹ * x₁ * d : ↥(centralizer ({w} : Set X))) : X) ∈ H :=
    mul_mem (mul_mem (inv_mem hdH) cfg.h₁) hdH
  have e : ρ ⟨((d⁻¹ * x₁ * d : ↥(centralizer ({w} : Set X))) : X), S.HN hyH⟩ =
      (ρ ⟨d, S.HN hdH⟩)⁻¹ * b1 S.m13 * ρ ⟨d, S.HN hdH⟩ := by
    have e1 := S.ρ_mul (mul_mem (inv_mem hdH) cfg.h₁) hdH
    rw [S.ρ_mul (inv_mem hdH) cfg.h₁, S.ρ_inv hdH, cfg.ρ₁] at e1
    exact e1
  have hπ : (ρ ⟨d, S.HN hdH⟩)⁻¹ * σ8 S.m13 = σ8 S.m13 * (ρ ⟨d, S.HN hdH⟩)⁻¹ :=
    (show Commute (ρ ⟨d, S.HN hdH⟩) (σ8 S.m13) from S.ρ_commute_σ8 hdH hdw).inv_left
  refine ⟨d⁻¹ * x₁ * d, hyH, ?_, ?_, ?_, ?_⟩
  · calc d⁻¹ * x₁ * d * (d⁻¹ * x₁ * d) = d⁻¹ * (x₁ * x₁) * d := by group
      _ = 1 := by rw [cfg.sq₁]; group
  · rw [e]
    have h := Perm.card_support_conj (σ := (ρ ⟨d, S.HN hdH⟩)⁻¹) (τ := b1 S.m13)
    rw [inv_inv] at h
    rw [h, card_support_b1]
  · rw [e]
    have hb := isBase_conj hπ (isBase_b1 (hm := S.m13))
    have hA := (alternatingGroup.normal (α := Fin m)).conj_mem _ (b1_mem S.m13)
      (ρ ⟨d, S.HN hdH⟩)⁻¹
    rw [inv_inv] at hb hA
    exact ⟨hb, hA⟩
  · rw [map_mul, map_mul, map_inv, hd, ← hns]
    rfl

theorem eq_of_ρ_eq [Finite X] {L : Subgroup ↥(permGrp H w)} {Syl : Sylow 2 ↥L}
    {y y' : ↥(centralizer ({w} : Set X))} (hy : (y : X) ∈ H) (hy' : (y' : X) ∈ H)
    (hρ : ρ ⟨y, S.HN hy⟩ = ρ ⟨y', S.HN hy'⟩) {s s' : ↥L} (hs : s ∈ (Syl : Subgroup ↥L))
    (hs' : s' ∈ (Syl : Subgroup ↥L)) (hys : toPermGrp H w y = s)
    (hys' : toPermGrp H w y' = s') : s = s' := by
  have hn : ((y⁻¹ * y' : ↥(centralizer ({w} : Set X))) : X) ∈ H := mul_mem (inv_mem hy) hy'
  have hn1 : ρ ⟨((y⁻¹ * y' : ↥(centralizer ({w} : Set X))) : X), S.HN hn⟩ = 1 := by
    have e := S.ρ_mul (inv_mem hy) hy'
    rw [S.ρ_inv hy, hρ, inv_mul_cancel] at e
    exact e
  have hodd := S.odd_orderOf_toPermGrp hn hn1
  rw [map_mul, map_inv, hys, hys'] at hodd
  have hodd' : Odd (orderOf (s⁻¹ * s')) := by
    rw [← orderOf_coe]
    exact hodd
  exact inv_mul_eq_one.mp
    (eq_one_of_odd_of_isPGroup Syl.isPGroup' (mul_mem (inv_mem hs) hs') hodd')

theorem card_center_le_seven [Finite X] (hc₀ : ∃ c₀ : X, c₀ * w = w * c₀ ∧ c₀ ∉ H)
    {x₁ x₂ c p : ↥(centralizer ({w} : Set X))} (cfg : S.Config x₁ x₂ c p)
    {L : Subgroup ↥(permGrp H w)} {Syl : Sylow 2 ↥L}
    (hSyl : (stabilizer ↥(permGrp H w) (basePt H w)).subgroupOf L =
      normalizer ((Syl : Subgroup ↥L) : Set ↥L))
    (hx₁L : toPermGrp H w x₁ ∈ L) {q k : ℕ} (hB : fusionBenderBorel ↥L q k) : q ≤ 7 := by
  obtain ⟨hSE, hZ2, hZcard, -⟩ := benderBorel_sylowCenter hB Syl
  have hσ1 : σ8 S.m13 ≠ 1 := fun h => by
    have := card_support_σ8 S.m13
    rw [h, Perm.support_one, Finset.card_empty] at this
    omega
  have hlift : ∀ s : ↥(sylowCenter (Syl : Subgroup ↥L)), ∃ (y : ↥(centralizer ({w} : Set X)))
      (hy : (y : X) ∈ H), ρ ⟨y, S.HN hy⟩ ∈ baseSubgroup S.m13 ∧ ρ ⟨y, S.HN hy⟩ ≠ σ8 S.m13 ∧
      toPermGrp H w y = ((s : ↥L) : ↥(permGrp H w)) := by
    intro s
    by_cases hs1 : (s : ↥L) = 1
    · have e : ρ ⟨((1 : ↥(centralizer ({w} : Set X))) : X), S.HN (one_mem H)⟩ = 1 := map_one ρ
      refine ⟨1, one_mem H, ?_, ?_, ?_⟩
      · rw [e]
        exact one_mem _
      · rw [e]
        exact hσ1.symm
      · simp [hs1]
    · have hsS : (s : ↥L) ∈ (Syl : Subgroup ↥L) := sylowCenter_le _ s.2
      obtain ⟨y, hy, -, hy4, hyb, hys⟩ := S.exists_base_of_involution hc₀ cfg hSyl hSE hx₁L
        (le_normalizer hsS) hs1 (hZ2 _ s.2)
      refine ⟨y, hy, hyb, fun h => ?_, hys⟩
      rw [h, card_support_σ8] at hy4
      omega
  choose f hfH hfb hf8 hfs using hlift
  let F : ↥(sylowCenter (Syl : Subgroup ↥L)) → ↥(baseSubgroup S.m13) := fun s => ⟨_, hfb s⟩
  have hF : Function.Injective F := fun s s' h => Subtype.ext (S.eq_of_ρ_eq (hfH s) (hfH s')
    (congrArg Subtype.val h) (sylowCenter_le _ s.2) (sylowCenter_le _ s'.2) (hfs s) (hfs s'))
  by_contra hq
  push Not at hq
  have hbij := hF.bijective_of_nat_card_le
    (by rw [hZcard]; exact (card_baseSubgroup_le S.m13).trans (by omega))
  obtain ⟨s, hs⟩ := hbij.2 ⟨σ8 S.m13, isBase_σ8, σ8_mem S.m13⟩
  exact hf8 s (congrArg Subtype.val hs)

theorem false_of_card_five [Finite X] (hc₀ : ∃ c₀ : X, c₀ * w = w * c₀ ∧ c₀ ∉ H)
    {x₁ x₂ c p : ↥(centralizer ({w} : Set X))} (cfg : S.Config x₁ x₂ c p)
    (h5 : Nat.card (Cos H w) = 5) : False := by
  classical
  have : Fintype (Cos H w) := Fintype.ofFinite _
  have hfix₁ := S.smul_eq_iff_of_four cfg.h₁ cfg.sq₁ cfg.four₁
  have hfix₂ := S.smul_eq_iff_of_four cfg.h₂ cfg.sq₂ cfg.four₂
  have hfix₃ := S.smul_eq_iff_of_four cfg.h₁₂ cfg.sq₁₂ cfg.four₁₂
  have hinv : ∀ u : ↥(centralizer ({w} : Set X)), u * u = 1 → ∀ ω : Cos H w,
      toPermGrp H w u • toPermGrp H w u • ω = ω := fun u hu ω => by
    rw [← mul_smul, ← map_mul, hu, map_one, one_smul]
  have : Nontrivial (Cos H w) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨β, hβ⟩ := exists_ne (basePt H w)
  have hα : ∀ u : ↥(centralizer ({w} : Set X)), u * u = 1 → (u : X) ∈ H →
      toPermGrp H w u • β ≠ basePt H w := fun u hu huH h => hβ (by
    have h' := congrArg (toPermGrp H w u • ·) h
    simp only [hinv u hu] at h'
    rw [h']
    exact (toPermGrp_mem_stabilizer_iff u).mpr huH)
  have hdist : ∀ u v : ↥(centralizer ({w} : Set X)), u * u = 1 →
      toPermGrp H w (u * v) • β ≠ β → toPermGrp H w u • β ≠ toPermGrp H w v • β :=
    fun u v hu huv h => huv (by rw [map_mul, mul_smul, ← h, hinv u hu])
  have hβ1 : toPermGrp H w x₁ • β ≠ β := fun h => hβ ((hfix₁ β).mp h)
  have hβ2 : toPermGrp H w x₂ • β ≠ β := fun h => hβ ((hfix₂ β).mp h)
  have hβ3 : toPermGrp H w (x₁ * x₂) • β ≠ β := fun h => hβ ((hfix₃ β).mp h)
  have h12 : toPermGrp H w x₁ • β ≠ toPermGrp H w x₂ • β := hdist x₁ x₂ cfg.sq₁ hβ3
  have h13 : toPermGrp H w x₁ • β ≠ toPermGrp H w (x₁ * x₂) • β :=
    hdist x₁ (x₁ * x₂) cfg.sq₁ (by rw [← mul_assoc, cfg.sq₁, one_mul]; exact hβ2)
  have h23 : toPermGrp H w x₂ • β ≠ toPermGrp H w (x₁ * x₂) • β :=
    hdist x₂ (x₁ * x₂) cfg.sq₂
      (by rw [← mul_assoc, ← cfg.c₁₂, mul_assoc, cfg.sq₂, mul_one]; exact hβ1)
  have hα1 := hα x₁ cfg.sq₁ cfg.h₁
  have hα2 := hα x₂ cfg.sq₂ cfg.h₂
  have hα3 := hα (x₁ * x₂) cfg.sq₁₂ cfg.h₁₂
  have hcard : ({basePt H w, β, toPermGrp H w x₁ • β, toPermGrp H w x₂ • β,
      toPermGrp H w (x₁ * x₂) • β} : Finset (Cos H w)).card = 5 := by
    have e2 := Finset.card_pair h23
    have e3 := Finset.card_insert_of_notMem
      (s := ({toPermGrp H w x₂ • β, toPermGrp H w (x₁ * x₂) • β} : Finset (Cos H w)))
      (a := toPermGrp H w x₁ • β)
      (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h12, h13⟩)
    have e4 := Finset.card_insert_of_notMem (s := ({toPermGrp H w x₁ • β, toPermGrp H w x₂ • β,
      toPermGrp H w (x₁ * x₂) • β} : Finset (Cos H w))) (a := β)
      (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hβ1.symm, hβ2.symm, hβ3.symm⟩)
    have e5 := Finset.card_insert_of_notMem (s := ({β, toPermGrp H w x₁ • β,
      toPermGrp H w x₂ • β, toPermGrp H w (x₁ * x₂) • β} : Finset (Cos H w))) (a := basePt H w)
      (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hβ.symm, hα1.symm, hα2.symm, hα3.symm⟩)
    omega
  have huniv := Finset.eq_univ_of_card _ (hcard.trans (by rw [← Nat.card_eq_fintype_card, h5]))
  have hmem : ∀ ω : Cos H w, ω = basePt H w ∨ ω = β ∨ ω = toPermGrp H w x₁ • β ∨
      ω = toPermGrp H w x₂ • β ∨ ω = toPermGrp H w (x₁ * x₂) • β := by
    intro ω
    have h := Finset.mem_univ ω
    rw [← huniv] at h
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  have hkey : ∀ (e : ↥(centralizer ({w} : Set X))) (heH : (e : X) ∈ H),
      IsBase S.m13 (ρ ⟨e, S.HN heH⟩) → e * e = 1 → e * x₁ = x₁ * e → e * x₂ = x₂ * e →
      toPermGrp H w p • β ≠ toPermGrp H w e • β := by
    intro e heH heb he2 he₁ he₂ hpe
    have hepH : ((e * p : ↥(centralizer ({w} : Set X))) : X) ∈ H := mul_mem heH cfg.hp
    have hhβ : toPermGrp H w (e * p) • β = β := by
      rw [map_mul, mul_smul, hpe, hinv e he2]
    have hhα : toPermGrp H w (e * p) • basePt H w = basePt H w :=
      (toPermGrp_mem_stabilizer_iff _).mpr hepH
    have hc : ∀ u : ↥(centralizer ({w} : Set X)), e * u = u * e → p * u = u * p →
        toPermGrp H w (e * p) * toPermGrp H w u = toPermGrp H w u * toPermGrp H w (e * p) :=
      fun u heu hpu => by
        have h : e * p * u = u * (e * p) := by
          calc e * p * u = e * (p * u) := mul_assoc _ _ _
            _ = e * (u * p) := by rw [hpu]
            _ = e * u * p := (mul_assoc _ _ _).symm
            _ = u * e * p := by rw [heu]
            _ = u * (e * p) := mul_assoc _ _ _
        rw [← map_mul, ← map_mul, h]
    have hcomm₃ : ∀ a : ↥(centralizer ({w} : Set X)), a * x₁ = x₁ * a → a * x₂ = x₂ * a →
        a * (x₁ * x₂) = x₁ * x₂ * a := fun a ha₁ ha₂ => by
      calc a * (x₁ * x₂) = a * x₁ * x₂ := (mul_assoc _ _ _).symm
        _ = x₁ * a * x₂ := by rw [ha₁]
        _ = x₁ * (a * x₂) := mul_assoc _ _ _
        _ = x₁ * (x₂ * a) := by rw [ha₂]
        _ = x₁ * x₂ * a := (mul_assoc _ _ _).symm
    have hc₁ := hc x₁ he₁ cfg.cp₁
    have hc₂ := hc x₂ he₂ cfg.cp₂
    have hc₃ := hc (x₁ * x₂) (hcomm₃ e he₁ he₂) (hcomm₃ p cfg.cp₁ cfg.cp₂)
    have hfixall : ∀ ω : Cos H w, toPermGrp H w (e * p) • ω = ω := by
      intro ω
      rcases hmem ω with rfl | rfl | rfl | rfl | rfl
      · exact hhα
      · exact hhβ
      · rw [← mul_smul, hc₁, mul_smul, hhβ]
      · rw [← mul_smul, hc₂, mul_smul, hhβ]
      · rw [← mul_smul, hc₃, mul_smul, hhβ]
    have h1 : toPermGrp H w (e * p) = 1 :=
      eq_of_smul_eq_smul (α := Cos H w) fun ω => by rw [hfixall, one_smul]
    have hcore := (toPermGrp_eq_one_iff _).mp h1
    have h8 := S.core_apply_of_ge hc₀ hcore (i := pt S.m13 8) (by simp [pt])
    have e1 : ρ ⟨((e * p : ↥(centralizer ({w} : Set X))) : X), S.HN (coreSubgroup_le hcore)⟩ =
        ρ ⟨e, S.HN heH⟩ * p1 S.m13 := by
      have e2 := S.ρ_mul heH cfg.hp
      rw [cfg.ρp] at e2
      exact e2
    rw [e1, Perm.mul_apply, p1_pt8, heb.apply_of_ge (by simp [pt])] at h8
    exact absurd (pt_injective S.m13 h8) (by decide)
  have e1 : ρ ⟨((1 : ↥(centralizer ({w} : Set X))) : X), S.HN (one_mem H)⟩ = 1 := map_one ρ
  rcases hmem (toPermGrp H w p • β) with h | h | h | h | h
  · exact hα p cfg.sqp cfg.hp h
  · refine hkey 1 (one_mem H) (by rw [e1]; exact isBase_one) (mul_one 1) (by simp) (by simp) ?_
    rw [h, map_one, one_smul]
  · exact hkey x₁ cfg.h₁ (by rw [cfg.ρ₁]; exact isBase_b1) cfg.sq₁ rfl cfg.c₁₂ h
  · exact hkey x₂ cfg.h₂ (by rw [cfg.ρ₂]; exact isBase_b2) cfg.sq₂ cfg.c₁₂.symm rfl h
  · refine hkey (x₁ * x₂) cfg.h₁₂ (by rw [cfg.ρ₁₂]; exact isBase_b1.mul isBase_b2) cfg.sq₁₂
      (by rw [mul_assoc, ← cfg.c₁₂]) (by rw [← mul_assoc x₂, ← cfg.c₁₂]) h

theorem false_of_unitary [Finite X] (hc₀ : ∃ c₀ : X, c₀ * w = w * c₀ ∧ c₀ ∉ H)
    {x₁ x₂ c p : ↥(centralizer ({w} : Set X))} (cfg : S.Config x₁ x₂ c p)
    {P : Sylow 2 ↥(centralizer ({w} : Set X))} (hwP : wC w ∈ P) (hx₁P : x₁ ∈ P) (hx₂P : x₂ ∈ P)
    {L : Subgroup ↥(permGrp H w)} [L.Normal] {Syl : Sylow 2 ↥L}
    (hSyl : (stabilizer ↥(permGrp H w) (basePt H w)).subgroupOf L =
      normalizer ((Syl : Subgroup ↥L) : Set ↥L))
    (hx₁L : toPermGrp H w x₁ ∈ L) (hx₂L : toPermGrp H w x₂ ∈ L) {q : ℕ} (hq : q = 4)
    (hB : fusionBenderBorel ↥L q 3) : False := by
  classical
  subst hq
  obtain ⟨hSE, -, hZcard, hScard⟩ := benderBorel_sylowCenter hB Syl
  have hx₁2 : (x₁ : X) * x₁ = 1 := congrArg Subtype.val cfg.sq₁
  let T : Subgroup X :=
    (P : Subgroup ↥(centralizer ({w} : Set X))).map (centralizer ({w} : Set X)).subtype
  have hT2 : IsPGroup 2 T := P.isPGroup'.map _
  have hPT : ∀ u ∈ (P : Subgroup ↥(centralizer ({w} : Set X))), (u : X) ∈ T :=
    fun u hu => ⟨u, hu, rfl⟩
  have hTH : T ≤ H := S.le_of_isPGroup hT2 (hPT x₁ hx₁P) cfg.h₁ hx₁2 cfg.four₁
  have hTw : ∀ u ∈ T, u * w = w * u := by
    rintro _ ⟨u, -, rfl⟩
    exact mem_centralizer_singleton_iff.mp u.2
  have hwT : w ∈ T := hPT _ hwP
  have hx₁W : (x₁ : X) ∈ wGroup S.m13 ρ T (hTH.trans S.HN) :=
    S.mem_wGroup hTH (hPT x₁ hx₁P) (by rw [cfg.ρ₁]; exact ⟨isBase_b1, b1_mem S.m13⟩)
  have hx₂W : (x₂ : X) ∈ wGroup S.m13 ρ T (hTH.trans S.HN) :=
    S.mem_wGroup hTH (hPT x₂ hx₂P) (by rw [cfg.ρ₂]; exact ⟨isBase_b2, b2_mem S.m13⟩)
  have hWcore : ∀ y ∈ wGroup S.m13 ρ T (hTH.trans S.HN), y ∈ coreSubgroup H w →
      y = 1 ∨ y = w := by
    intro y hy hyc
    by_contra h
    push Not at h
    obtain ⟨hy2, hy4⟩ := S.wGroup_four hT2 hTH hwT hy h.1 h.2
    exact S.not_mem_coreSubgroup_of_four hc₀ (hTH hy.1) hy2 hy4 hyc
  let ψT : Sylow 2 ↥(permGrp H w) := P.mapSurjective toPermGrp_surjective
  let S' : Sylow 2 ↥L := QuasiDihedralFusion.sylowInfNormal ψT L
  have hS' : ∀ s : ↥L, s ∈ (S' : Subgroup ↥L) ↔
      ∃ u ∈ (P : Subgroup ↥(centralizer ({w} : Set X))), toPermGrp H w u = s := by
    intro s
    rw [QuasiDihedralFusion.sylowInfNormal_coe, mem_subgroupOf, Sylow.coe_mapSurjective, mem_map]
  have hS'N : (S' : Subgroup ↥L) ≤ normalizer ((Syl : Subgroup ↥L) : Set ↥L) := by
    intro s hs
    obtain ⟨u, hu, hus⟩ := (hS' s).mp hs
    rw [← hSyl, mem_subgroupOf, ← hus]
    exact (toPermGrp_mem_stabilizer_iff u).mpr (hTH (hPT u hu))
  have hS'S : (S' : Subgroup ↥L) ≤ Syl := by
    have h : (S' : Subgroup ↥L) ⊓ normalizer ((Syl : Subgroup ↥L) : Set ↥L) =
        (S' : Subgroup ↥L) ⊓ Syl := S'.isPGroup'.inf_normalizer_sylow Syl
    intro s hs
    have hmem : s ∈ (S' : Subgroup ↥L) ⊓ normalizer ((Syl : Subgroup ↥L) : Set ↥L) :=
      ⟨hs, hS'N hs⟩
    rw [h] at hmem
    exact hmem.2
  have hSS' : (Syl : Subgroup ↥L) = S' := S'.is_maximal' Syl.isPGroup' hS'S
  have hlift : ∀ s ∈ (Syl : Subgroup ↥L),
      ∃ u ∈ (P : Subgroup ↥(centralizer ({w} : Set X))), toPermGrp H w u = s := by
    intro s hs
    rw [hSS'] at hs
    exact (hS' s).mp hs
  have hmemSyl : ∀ u ∈ (P : Subgroup ↥(centralizer ({w} : Set X))),
      ∀ hL : toPermGrp H w u ∈ L, (⟨_, hL⟩ : ↥L) ∈ (Syl : Subgroup ↥L) := by
    intro u hu hL
    rw [hSS']
    exact (hS' _).mpr ⟨u, hu, rfl⟩
  have hzZ : ∀ u ∈ (P : Subgroup ↥(centralizer ({w} : Set X))), u * u = 1 →
      ∀ hL : toPermGrp H w u ∈ L, (⟨_, hL⟩ : ↥L) ∈ sylowCenter (Syl : Subgroup ↥L) :=
    fun u hu hu2 hL => mem_sylowCenter_of_sq_eq_one hB (by norm_num) Syl (hmemSyl u hu hL)
      (Subtype.ext (by
        change toPermGrp H w u ^ 2 = 1
        rw [sq, ← map_mul, hu2, map_one]))
  have hz₁Z := hzZ x₁ hx₁P cfg.sq₁ hx₁L
  have hz₂Z := hzZ x₂ hx₂P cfg.sq₂ hx₂L
  have hcomm : ∀ u ∈ (P : Subgroup ↥(centralizer ({w} : Set X))), toPermGrp H w u ∈ L →
      ∀ x : ↥(centralizer ({w} : Set X)), (x : X) ∈ wGroup S.m13 ρ T (hTH.trans S.HN) →
      ∀ hxL : toPermGrp H w x ∈ L, (⟨_, hxL⟩ : ↥L) ∈ sylowCenter (Syl : Subgroup ↥L) →
      u * x * u⁻¹ * x⁻¹ = 1 ∨ u * x * u⁻¹ * x⁻¹ = wC w := by
    intro u hu huL x hxW hxL hxZ
    have hc : toPermGrp H w u * toPermGrp H w x = toPermGrp H w x * toPermGrp H w u :=
      congrArg Subtype.val ((mem_sylowCenter.mp hxZ).2 ⟨_, huL⟩ (hmemSyl u hu huL))
    have h1 : toPermGrp H w (u * x * u⁻¹ * x⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hc]
      group
    have hcore := (toPermGrp_eq_one_iff _).mp h1
    have hW : ((u * x * u⁻¹ * x⁻¹ : ↥(centralizer ({w} : Set X))) : X) ∈
        wGroup S.m13 ρ T (hTH.trans S.HN) :=
      mul_mem (S.conj_mem_wGroup hTH hTw (hPT u hu) hxW) (inv_mem hxW)
    rcases hWcore _ hW hcore with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hsq : ∀ u ∈ (P : Subgroup ↥(centralizer ({w} : Set X))), u * x₁ = x₁ * u →
      u * x₂ = x₂ * u → toPermGrp H w u ∈ L → toPermGrp H w u ^ 2 = 1 := by
    intro u hu hu₁ hu₂ huL
    have huH : (u : X) ∈ H := hTH (hPT u hu)
    have hρu : ∀ i : Fin m, (i : ℕ) < 8 → ρ ⟨u, S.HN huH⟩ (ρ ⟨u, S.HN huH⟩ i) = i := by
      intro i hi
      have hc8 := S.ρ_commute_σ8 huH (mem_centralizer_singleton_iff.mp u.2)
      have hc1 : ρ ⟨u, S.HN huH⟩ * b1 S.m13 = b1 S.m13 * ρ ⟨u, S.HN huH⟩ := by
        rw [← cfg.ρ₁, ← S.ρ_mul huH cfg.h₁, ← S.ρ_mul cfg.h₁ huH]
        congr 1
        exact Subtype.ext (show (u : X) * x₁ = x₁ * u from congrArg Subtype.val hu₁)
      have hc2 : ρ ⟨u, S.HN huH⟩ * b2 S.m13 = b2 S.m13 * ρ ⟨u, S.HN huH⟩ := by
        rw [← cfg.ρ₂, ← S.ρ_mul huH cfg.h₂, ← S.ρ_mul cfg.h₂ huH]
        congr 1
        exact Subtype.ext (show (u : X) * x₂ = x₂ * u from congrArg Subtype.val hu₂)
      rcases apply_of_commute_base hc8 hc1 hc2 hi with h | h
      · rw [h, h]
      · rw [h, ← Perm.mul_apply, hc8, Perm.mul_apply, h, σ8_σ8]
    by_contra hne
    have hvP : u * u ∈ (P : Subgroup ↥(centralizer ({w} : Set X))) := mul_mem hu hu
    have hvL : toPermGrp H w (u * u) ∈ L := by
      rw [map_mul]
      exact mul_mem huL huL
    let g : ↥L := ⟨toPermGrp H w (u * u), hvL⟩
    have hgS : g ∈ (Syl : Subgroup ↥L) := hmemSyl _ hvP hvL
    have hg1 : g ≠ 1 := fun h => hne (by rw [sq, ← map_mul]; exact congrArg Subtype.val h)
    have hgo : orderOf g ≠ 0 := (orderOf_pos g).ne'
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp Syl.isPGroup') ⟨g, hgS⟩
    rw [orderOf_mk] at hk
    have h2 : 2 ∣ orderOf g := by
      rcases k with _ | k
      · rw [pow_zero, orderOf_eq_one_iff] at hk
        exact absurd hk hg1
      · rw [hk, pow_succ]
        exact dvd_mul_left 2 _
    have hsN : orderOf (g ^ (orderOf g / 2)) = 2 := orderOf_pow_orderOf_div hgo h2
    have hsS : g ^ (orderOf g / 2) ∈ (Syl : Subgroup ↥L) := pow_mem hgS _
    have hs1 : g ^ (orderOf g / 2) ≠ 1 := fun h => by
      rw [h, orderOf_one] at hsN
      omega
    have hs2 : (g ^ (orderOf g / 2)) ^ 2 = 1 := by
      have h := pow_orderOf_eq_one (g ^ (orderOf g / 2))
      rwa [hsN] at h
    obtain ⟨y, hyH, -, -, hyb, hys⟩ := S.exists_base_of_involution hc₀ cfg hSyl hSE hx₁L
      (le_normalizer hsS) hs1 hs2
    have hvN : toPermGrp H w ((u * u) ^ (orderOf g / 2)) =
        ((g ^ (orderOf g / 2) : ↥L) : ↥(permGrp H w)) := by
      rw [map_pow]
      rfl
    have h1 : toPermGrp H w (y⁻¹ * (u * u) ^ (orderOf g / 2)) = 1 := by
      rw [map_mul, map_inv, hys, hvN, inv_mul_cancel]
    have hcore := (toPermGrp_eq_one_iff _).mp h1
    have hvNH : (((u * u) ^ (orderOf g / 2) : ↥(centralizer ({w} : Set X))) : X) ∈ H :=
      pow_mem (mul_mem huH huH) _
    have hρ1 : ρ ⟨(((u * u) ^ (orderOf g / 2) : ↥(centralizer ({w} : Set X))) : X),
        S.HN hvNH⟩ = 1 := by
      refine Equiv.ext fun i => ?_
      rw [Perm.one_apply]
      rcases lt_or_ge (i : ℕ) 8 with hi | hi
      · have e : ρ ⟨(((u * u) ^ (orderOf g / 2) : ↥(centralizer ({w} : Set X))) : X),
            S.HN hvNH⟩ = (ρ ⟨u, S.HN huH⟩ * ρ ⟨u, S.HN huH⟩) ^ (orderOf g / 2) := by
          have e1 := S.ρ_pow (mul_mem huH huH) (orderOf g / 2)
          rw [S.ρ_mul huH huH] at e1
          exact e1
        rw [e]
        exact Perm.pow_apply_eq_self_of_apply_eq_self (by rw [Perm.mul_apply]; exact hρu i hi) _
      · have h8 := S.core_apply_of_ge hc₀ hcore hi
        have e : ρ ⟨(((u * u) ^ (orderOf g / 2) : ↥(centralizer ({w} : Set X))) : X),
            S.HN hvNH⟩ = ρ ⟨y, S.HN hyH⟩ * ρ ⟨((y⁻¹ * (u * u) ^ (orderOf g / 2) :
              ↥(centralizer ({w} : Set X))) : X), S.HN (coreSubgroup_le hcore)⟩ := by
          rw [← S.ρ_mul hyH (coreSubgroup_le hcore)]
          congr 1
          apply Subtype.ext
          simp
        rw [e, Perm.mul_apply, h8]
        exact (mem_baseSubgroup.mp hyb).1.apply_of_ge hi
    have h2k : ∃ j : ℕ, ((((u * u) ^ (orderOf g / 2) : ↥(centralizer ({w} : Set X))) : X)) ^
        2 ^ j = 1 := by
      obtain ⟨j, hj⟩ := P.isPGroup' ⟨_, pow_mem hvP (orderOf g / 2)⟩
      exact ⟨j, by simpa using congrArg (fun a : ↥(P : Subgroup ↥(centralizer ({w} : Set X))) =>
        ((a : ↥(centralizer ({w} : Set X))) : X)) hj⟩
    have hv1 := S.eq_one_of_ρ_eq_one hvNH h2k hρ1
    have hvN1 : (u * u) ^ (orderOf g / 2) = 1 := Subtype.ext hv1
    exact hs1 (Subtype.ext (by rw [← hvN, hvN1]; simp))
  let cls : ↥(centralizer ({w} : Set X)) → Bool × Bool := fun u =>
    (decide (u * x₁ = x₁ * u), decide (u * x₂ = x₂ * u))
  have hrep : ∀ cl : Bool × Bool, ∃ r ∈ (P : Subgroup ↥(centralizer ({w} : Set X))),
      ∃ _ : toPermGrp H w r ∈ L, ∀ u ∈ (P : Subgroup ↥(centralizer ({w} : Set X))),
        toPermGrp H w u ∈ L → cls u = cl → cls r = cl := by
    intro cl
    by_cases h : ∃ u ∈ (P : Subgroup ↥(centralizer ({w} : Set X))), toPermGrp H w u ∈ L ∧
      cls u = cl
    · obtain ⟨u, hu, huL, hucl⟩ := h
      exact ⟨u, hu, huL, fun _ _ _ _ => hucl⟩
    · refine ⟨1, one_mem _, by rw [map_one]; exact one_mem L, fun u hu huL hucl => ?_⟩
      exact absurd ⟨u, hu, huL, hucl⟩ h
  choose rep hrepP hrepL hrepC using hrep
  let F : (Bool × Bool) × ↥(sylowCenter (Syl : Subgroup ↥L)) → ↥(Syl : Subgroup ↥L) := fun a =>
    ⟨⟨toPermGrp H w (rep a.1), hrepL a.1⟩ * (a.2 : ↥L),
      mul_mem (hmemSyl _ (hrepP a.1) (hrepL a.1)) (sylowCenter_le _ a.2.2)⟩
  have hF : Function.Surjective F := by
    rintro ⟨s, hs⟩
    obtain ⟨u, hu, hus⟩ := hlift s hs
    have huL : toPermGrp H w u ∈ L := by
      rw [hus]
      exact s.2
    have hrc : cls (rep (cls u)) = cls u := hrepC (cls u) u hu huL rfl
    have hrP := hrepP (cls u)
    have hrL := hrepL (cls u)
    have hiff₁ : rep (cls u) * x₁ = x₁ * rep (cls u) ↔ u * x₁ = x₁ * u :=
      decide_eq_decide.mp (congrArg Prod.fst hrc)
    have hiff₂ : rep (cls u) * x₂ = x₂ * rep (cls u) ↔ u * x₂ = x₂ * u :=
      decide_eq_decide.mp (congrArg Prod.snd hrc)
    have hd₁ := commute_inv_mul_of_conj (hcomm _ hrP hrL x₁ hx₁W hx₁L hz₁Z)
      (hcomm u hu huL x₁ hx₁W hx₁L hz₁Z) hiff₁
    have hd₂ := commute_inv_mul_of_conj (hcomm _ hrP hrL x₂ hx₂W hx₂L hz₂Z)
      (hcomm u hu huL x₂ hx₂W hx₂L hz₂Z) hiff₂
    have hdP : (rep (cls u))⁻¹ * u ∈ (P : Subgroup ↥(centralizer ({w} : Set X))) :=
      mul_mem (inv_mem hrP) hu
    have hdL : toPermGrp H w ((rep (cls u))⁻¹ * u) ∈ L := by
      rw [map_mul, map_inv]
      exact mul_mem (inv_mem hrL) huL
    have hdZ : (⟨_, hdL⟩ : ↥L) ∈ sylowCenter (Syl : Subgroup ↥L) :=
      mem_sylowCenter_of_sq_eq_one hB (by norm_num) Syl (hmemSyl _ hdP hdL)
        (Subtype.ext (hsq _ hdP hd₁ hd₂ hdL))
    refine ⟨(cls u, ⟨_, hdZ⟩), Subtype.ext (Subtype.ext ?_)⟩
    change toPermGrp H w (rep (cls u)) * toPermGrp H w ((rep (cls u))⁻¹ * u) =
      (s : ↥(permGrp H w))
    rw [map_mul, map_inv, mul_inv_cancel_left, hus]
  have hcard := Nat.card_le_card_of_surjective F hF
  rw [Nat.card_prod, Nat.card_prod, hZcard, hScard, Nat.card_eq_fintype_card (α := Bool),
    Fintype.card_bool] at hcard
  norm_num at hcard


theorem aschbacher [Finite X] (hc₀ : ∃ c₀ : X, c₀ * w = w * c₀ ∧ c₀ ∉ H)
    {x₁ x₂ c p : ↥(centralizer ({w} : Set X))} (cfg : S.Config x₁ x₂ c p) :
    fusionIsBenderGroup ↥(normalClosure ({toPermGrp H w x₁} : Set ↥(permGrp H w))) ∧
      IsPretransitive ↥(normalClosure ({toPermGrp H w x₁} : Set ↥(permGrp H w))) (Cos H w) ∧
      BenderSuzuki.IsBorelSubgroup ((stabilizer ↥(permGrp H w) (basePt H w)).subgroupOf
        (normalClosure ({toPermGrp H w x₁} : Set ↥(permGrp H w)))) := by
  have hx₁2 : (x₁ : X) * x₁ = 1 := congrArg Subtype.val cfg.sq₁
  have hz1 : toPermGrp H w x₁ ≠ 1 := fun h => S.not_mem_coreSubgroup_of_four hc₀ cfg.h₁ hx₁2
    cfg.four₁ ((toPermGrp_eq_one_iff x₁).mp h)
  have hz2 : toPermGrp H w x₁ ^ 2 = 1 := by rw [sq, ← map_mul, cfg.sq₁, map_one]
  have hz : orderOf (toPermGrp H w x₁) = 2 := orderOf_eq_prime hz2 hz1
  have hzQ : toPermGrp H w x₁ ∈ S.Qgrp :=
    ⟨x₁, mem_subgroupOf.mpr ⟨⟨cfg.h₁, x₁.2⟩, by
      show ρ ⟨(x₁ : X), _⟩ ∈ baseSubgroup S.m13
      rw [cfg.ρ₁]
      exact ⟨isBase_b1, b1_mem S.m13⟩⟩, rfl⟩
  have hconj : toPermGrp H w c * toPermGrp H w x₁ * (toPermGrp H w c)⁻¹ = toPermGrp H w x₂ := by
    rw [← map_inv, ← map_mul, ← map_mul, cfg.conj]
  have hne : toPermGrp H w c * toPermGrp H w x₁ * (toPermGrp H w c)⁻¹ ≠ toPermGrp H w x₁ := by
    rw [hconj]
    intro h
    have h12 : toPermGrp H w (x₁ * x₂) = 1 := by rw [map_mul, h, ← map_mul, cfg.sq₁, map_one]
    exact S.not_mem_coreSubgroup_of_four hc₀ cfg.h₁₂ (congrArg Subtype.val cfg.sq₁₂) cfg.four₁₂
      ((toPermGrp_eq_one_iff _).mp h12)
  have hcomm : Commute (toPermGrp H w x₁)
      (toPermGrp H w c * toPermGrp H w x₁ * (toPermGrp H w c)⁻¹) := by
    rw [hconj]
    show toPermGrp H w x₁ * toPermGrp H w x₂ = toPermGrp H w x₂ * toPermGrp H w x₁
    rw [← map_mul, ← map_mul, cfg.c₁₂]
  exact CFSG.Holt.General.aschbacher73_theorem2_of_commute (fun q hq hq2 ω => S.Q_fix hq hq2 ω)
    S.stabilizer_le_normalizer_Q hzQ hz hne hcomm

theorem centralizer_le [Finite X] : centralizer ({w} : Set X) ≤ H := by
  intro c₀ hc₀w
  by_contra hc₀H
  have hc₀ : ∃ c₀ : X, c₀ * w = w * c₀ ∧ c₀ ∉ H :=
    ⟨c₀, mem_centralizer_singleton_iff.mp hc₀w, hc₀H⟩
  obtain ⟨x₁, x₂, c, p, cfg⟩ := S.exists_config
  obtain ⟨P, hwP, hx₁P, hx₂P⟩ := S.exists_sylow cfg
  obtain ⟨hBen, htr, -, Syl, hSyl⟩ := S.aschbacher hc₀ cfg
  have hx₁L : toPermGrp H w x₁ ∈ normalClosure ({toPermGrp H w x₁} : Set ↥(permGrp H w)) :=
    subset_normalClosure rfl
  have hx₂L : toPermGrp H w x₂ ∈ normalClosure ({toPermGrp H w x₁} : Set ↥(permGrp H w)) := by
    have h := normalClosure_normal.conj_mem _ hx₁L (toPermGrp H w c)
    rwa [← map_inv, ← map_mul, ← map_mul, cfg.conj] at h
  have hq7 : ∀ {q k : ℕ},
      fusionBenderBorel ↥(normalClosure ({toPermGrp H w x₁} : Set ↥(permGrp H w))) q k → q ≤ 7 :=
    fun hB => S.card_center_le_seven hc₀ cfg hSyl hx₁L hB
  have hBen' := hBen
  rcases hBen with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  ·
    have : Finite PSL(2, GaloisField 2 f) := Finite.of_equiv _ e.toEquiv
    have hB := (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1
      f hf).map_mulEquiv e.symm
    have hf2 : f = 2 := by
      have h7 := hq7 hB
      by_contra h
      have : 8 ≤ 2 ^ f :=
        (show 8 = 2 ^ 3 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨-, -, -, hScard⟩ := benderBorel_sylowCenter hB Syl
    have hsyl : Nat.card (Sylow 2 ↥(normalClosure ({toPermGrp H w x₁} : Set ↥(permGrp H w)))) =
        5 := by
      simp [CFSG.Goldschmidt.GoldType.card_sylow_of_bender hBen' Syl, hScard, hf2]
    have hstab : stabilizer ↥(normalClosure ({toPermGrp H w x₁} : Set ↥(permGrp H w)))
        (basePt H w) = (stabilizer ↥(permGrp H w) (basePt H w)).subgroupOf
          (normalClosure ({toPermGrp H w x₁} : Set ↥(permGrp H w))) := by
      ext ℓ
      rw [mem_stabilizer_iff, mem_subgroupOf, mem_stabilizer_iff, Subgroup.smul_def]
    have h5 : Nat.card (Cos H w) = 5 := by
      rw [← index_stabilizer_of_transitive
        ↥(normalClosure ({toPermGrp H w x₁} : Set ↥(permGrp H w))) (basePt H w), hstab, hSyl]
      exact (Sylow.card_eq_index_normalizer Syl).symm.trans hsyl
    exact S.false_of_card_five hc₀ cfg h5
  ·
    have : Finite (PSU3 2 f) := Finite.of_equiv _ e.toEquiv
    have hB := (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_2
      f hf).map_mulEquiv e.symm
    have hf2 : f = 2 := by
      have h7 := hq7 hB
      by_contra h
      have : 8 ≤ 2 ^ f :=
        (show 8 = 2 ^ 3 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact S.false_of_unitary hc₀ cfg hwP hx₁P hx₂P hSyl hx₁L hx₂L (by rw [hf2]; norm_num) hB
  ·
    have : Finite (Sz a) := Finite.of_equiv _ e.toEquiv
    have hB := (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_4
      a ha).map_mulEquiv e.symm
    have h7 := hq7 hB
    have : 8 ≤ 2 ^ (2 * a + 1) :=
      (show 8 = 2 ^ 3 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

end Setup


theorem centralizer_le_of_eight [Finite X] (hρ : IsPermAction θ ρ) (hm : 13 ≤ m) (hMH : M ≤ H)
    (hHN : H ≤ normalizer (M : Set X))
    (hker : ∀ g ∈ H, g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g)) (htH : t ∈ H)
    (ht2 : t * t = 1) (ht4 : (ρ ⟨t, hHN htH⟩).support.card = 4)
    (hfus : ∀ g : X, g * t * g⁻¹ ∈ H → g ∈ H) (hsyl : ∃ P : Sylow 2 X, (P : Subgroup X) ≤ H)
    {v : X} (hvH : v ∈ H) (hv2 : v * v = 1) (hv8 : (ρ ⟨v, hHN hvH⟩).support.card = 8) :
    centralizer ({v} : Set X) ≤ H := by
  have hρv2 : ρ ⟨v, hHN hvH⟩ * ρ ⟨v, hHN hvH⟩ = 1 := by
    rw [← map_mul, show (⟨v, hHN hvH⟩ : ↥(normalizer (M : Set X))) * ⟨v, hHN hvH⟩ = 1 from
      Subtype.ext hv2, map_one]
  obtain ⟨π, hπ⟩ := exists_alt_conj_of_eight (by omega) hρv2 (σ8_mul_self hm) hv8
    (card_support_σ8 hm)
  have h1 : ρ ⟨1, one_mem _⟩ = 1 := map_one ρ
  obtain ⟨y, hyM, -, hyπ⟩ := hρ.exists_lift_perm (by omega) (one_mem _) (mul_one 1) π.2
    (by rw [h1, mul_one, one_mul])
  have hyH : y ∈ H := hMH hyM
  have hwH : y * v * y⁻¹ ∈ H := mul_mem (mul_mem hyH hvH) (inv_mem hyH)
  have hρw : ρ ⟨y * v * y⁻¹, hHN hwH⟩ = σ8 hm := by
    have e : ρ ⟨y * v * y⁻¹, hHN hwH⟩ =
        ρ ⟨y, hHN hyH⟩ * ρ ⟨v, hHN hvH⟩ * (ρ ⟨y, hHN hyH⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    have e' : ρ ⟨y, hHN hyH⟩ = π := hyπ
    rw [e, e', hπ]
  have hw2 : y * v * y⁻¹ * (y * v * y⁻¹) = 1 := by
    calc y * v * y⁻¹ * (y * v * y⁻¹) = y * (v * v) * y⁻¹ := by group
      _ = 1 := by rw [hv2]; group
  have S : Setup H M θ ρ t (y * v * y⁻¹) :=
    { perm := hρ, m13 := hm, MH := hMH, HN := hHN, ker := hker, tH := htH, t2 := ht2,
      t4 := ht4, fus := hfus, syl := hsyl, wH := hwH, w2 := hw2, wσ := hρw }
  intro c hc
  have hcv : c * v = v * c := mem_centralizer_singleton_iff.mp hc
  have hc' : y * c * y⁻¹ ∈ centralizer ({y * v * y⁻¹} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    calc y * c * y⁻¹ * (y * v * y⁻¹) = y * (c * v) * y⁻¹ := by group
      _ = y * (v * c) * y⁻¹ := by rw [hcv]
      _ = y * v * y⁻¹ * (y * c * y⁻¹) := by group
  have h := mul_mem (mul_mem (inv_mem hyH) (S.centralizer_le hc')) hyH
  rwa [show y⁻¹ * (y * c * y⁻¹) * y = c by group] at h

end CaseTwoW

theorem signalizerCaseTwoWInput_holds
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) : SignalizerCaseTwoWInput := by
  intro X _ _ _ t J n e E D S hWne M θ ρ hρ hMH hMpc hJM hHN hk hA4 hfus hSyl g hgH hne hcomm
    hconj
  have hn9 := S.nine_le
  have htord : orderOf t = 2 := S.pair.1.1
  have ht2 : t * t = 1 := by rw [← sq, ← htord, pow_orderOf_eq_one]
  have htH : t ∈ normalizer (Sol78.signalizerCompletion E E : Set X) :=
    CaseTwo.mem_of_conj_mem_of_sylow htord hfus hSyl
  have ht4 : (ρ ⟨t, hHN htH⟩).support.card = 4 :=
    S.card_support_t_of_add_four hT13 hML hSch hMH hMpc (hHN htH) hJM hρ
  have hgH' : g ∈ normalizer (Sol78.signalizerCompletion E E : Set X) := hfus g hgH
  have hsq : ∀ (x : X) (hx : x ∈ normalizer (Sol78.signalizerCompletion E E : Set X)),
      x * x = 1 → ρ ⟨x, hHN hx⟩ * ρ ⟨x, hHN hx⟩ = 1 := fun x hx h => by
    rw [← map_mul, show (⟨x, hHN hx⟩ : ↥(normalizer (M : Set X))) * ⟨x, hHN hx⟩ = 1 from
      Subtype.ext h, map_one]
  have ht'2 : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hρt' : ρ ⟨g * t * g⁻¹, hHN hgH⟩ =
      ρ ⟨g, hHN hgH'⟩ * ρ ⟨t, hHN htH⟩ * (ρ ⟨g, hHN hgH'⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have ht'4 : (ρ ⟨g * t * g⁻¹, hHN hgH⟩).support.card = 4 := by
    rw [hρt', Perm.card_support_conj, ht4]
  have hwH : t * (g * t * g⁻¹) ∈ normalizer (Sol78.signalizerCompletion E E : Set X) :=
    mul_mem htH hgH
  have hw2 : t * (g * t * g⁻¹) * (t * (g * t * g⁻¹)) = 1 := by
    calc t * (g * t * g⁻¹) * (t * (g * t * g⁻¹)) =
        t * (g * t * g⁻¹ * t) * (g * t * g⁻¹) := by group
      _ = t * (t * (g * t * g⁻¹)) * (g * t * g⁻¹) := by rw [hcomm]
      _ = t * t * (g * t * g⁻¹ * (g * t * g⁻¹)) := by group
      _ = 1 := by rw [ht2, ht'2, one_mul]
  have hρw : ρ ⟨t * (g * t * g⁻¹), hHN hwH⟩ = ρ ⟨t, hHN htH⟩ * ρ ⟨g * t * g⁻¹, hHN hgH⟩ := by
    rw [← map_mul]
    rfl
  have hA : ρ ⟨t * (g * t * g⁻¹), hHN hwH⟩ ∈ alternatingGroup (Fin (n + 4)) := by
    rw [hρw]
    exact mul_mem (mem_alternatingGroup_of_four (hsq t htH ht2) ht4)
      (mem_alternatingGroup_of_four (hsq _ hgH ht'2) ht'4)
  have hdvd := four_dvd_card_support_of_mem_alternating (hsq _ hwH hw2) hA
  have hle : (ρ ⟨t * (g * t * g⁻¹), hHN hwH⟩).support.card ≤ 8 := by
    rw [hρw]
    calc _ ≤ ((ρ ⟨t, hHN htH⟩).support ∪ (ρ ⟨g * t * g⁻¹, hHN hgH⟩).support).card :=
          Finset.card_le_card (Perm.support_mul_le _ _)
      _ ≤ (ρ ⟨t, hHN htH⟩).support.card + (ρ ⟨g * t * g⁻¹, hHN hgH⟩).support.card :=
          Finset.card_union_le _ _
      _ = 8 := by rw [ht4, ht'4]
  have h0 : (ρ ⟨t * (g * t * g⁻¹), hHN hwH⟩).support.card ≠ 0 := by
    intro h0
    have h1 : ρ ⟨t * (g * t * g⁻¹), hHN hwH⟩ = 1 :=
      Perm.support_eq_empty_iff.mp (Finset.card_eq_zero.mp h0)
    have hodd := hk _ hwH (hρ.mem_coreActionKernel _ h1)
    have hw1 : t * (g * t * g⁻¹) = 1 := by
      have hdvd2 : orderOf (t * (g * t * g⁻¹)) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hw2)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
      · exact orderOf_eq_one_iff.mp h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    apply hne
    calc g * t * g⁻¹ = t⁻¹ * (t * (g * t * g⁻¹)) := by group
      _ = t := by rw [hw1, mul_one]; exact inv_eq_of_mul_eq_one_right ht2
  have h4 : (ρ ⟨t * (g * t * g⁻¹), hHN hwH⟩).support.card ≠ 4 := by
    intro h4
    obtain ⟨c, -, hc⟩ := hρ.exists_conj_of_four (by omega) hMH hk (hHN htH) (hHN hwH) htH hwH
      ht2 hw2 ht4 h4
    exact hconj c hc
  exact CaseTwoW.centralizer_le_of_eight hρ (by omega) hMH hHN hk htH ht2 ht4 hfus hSyl hwH hw2
    (by omega)

end CFSG.ComponentClassification.SolMax
