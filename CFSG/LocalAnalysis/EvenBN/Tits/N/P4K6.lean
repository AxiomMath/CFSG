module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Base
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Perm
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Y

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup IsF20
open scoped Pointwise

section K6

variable {Γ : Type*} [Group Γ] {U : Subgroup Γ} {x v t : Γ}

theorem eq_one_or_eq_of_mem_zpowers_invol (htt : t * t = 1) {y : Γ} (hy : y ∈ zpowers t) :
    y = 1 ∨ y = t := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact htt
  have key : t ^ n = t ^ (n % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 2]
    rw [zpow_add, zpow_mul, ht2, one_zpow, mul_one]
  rw [key]
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

theorem mem_normalizer_of_comm {S : Subgroup Γ} {g : Γ} (hg : ∀ s ∈ S, g * s = s * g) :
    g ∈ normalizer (S : Set Γ) :=
  Subgroup.centralizer_le_normalizer (S : Set Γ) (mem_centralizer_iff.2 fun s hs => (hg s hs).symm)

theorem mem_sup_zpowers_iff_of_comm_invol (htt : t * t = 1) (htU : ∀ u ∈ U, t * u = u * t) {y : Γ} :
    y ∈ U ⊔ zpowers t ↔ y ∈ U ∨ t * y ∈ U := by
  have hnorm : zpowers t ≤ normalizer (U : Set Γ) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_of_comm htU
  have hset : (U : Set Γ) * (zpowers t : Set Γ) = ((U ⊔ zpowers t : Subgroup Γ) : Set Γ) :=
    (Subgroup.coe_mul_of_right_le_normalizer_left U (zpowers t) hnorm).symm
  constructor
  · intro hy
    have hy' : y ∈ (U : Set Γ) * (zpowers t : Set Γ) := by rw [hset]; exact hy
    obtain ⟨u, hu, s, hs, hys⟩ := hy'
    have hys' : u * s = y := hys
    rcases eq_one_or_eq_of_mem_zpowers_invol htt hs with h | h
    · left
      rw [← hys', h, mul_one]
      exact hu
    · right
      rw [← hys', h]
      have : t * (u * t) = u := by rw [← htU u hu, ← mul_assoc, htt, one_mul]
      rw [this]
      exact hu
  · rintro (hy | hy)
    · exact mem_sup_left hy
    · have e : y = t * (t * y) := by rw [← mul_assoc, htt, one_mul]
      rw [e]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hy)

theorem comm_of_mem_sup_zpowers (hF : IsF20 U x v) (htt : t * t = 1) (htU : ∀ u ∈ U, t * u = u * t)
    {a b : Γ} (ha : a ∈ U ⊔ zpowers t) (hb : b ∈ U ⊔ zpowers t) : a * b = b * a := by
  rw [mem_sup_zpowers_iff_of_comm_invol htt htU] at ha hb
  have ha' : ∃ u ∈ U, a = u ∨ a = t * u := by
    rcases ha with h | h
    · exact ⟨a, h, Or.inl rfl⟩
    · exact ⟨t * a, h, Or.inr (by rw [← mul_assoc, htt, one_mul])⟩
  have hb' : ∃ u ∈ U, b = u ∨ b = t * u := by
    rcases hb with h | h
    · exact ⟨b, h, Or.inl rfl⟩
    · exact ⟨t * b, h, Or.inr (by rw [← mul_assoc, htt, one_mul])⟩
  obtain ⟨u, hu, hau⟩ := ha'
  obtain ⟨u', hu', hbu⟩ := hb'
  have hc := hF.comm u hu u' hu'
  have h1 := htU u hu
  have h2 := htU u' hu'
  rcases hau with hau | hau <;> rcases hbu with hbu | hbu
  · rw [hau, hbu]
    exact hc
  · rw [hau, hbu]
    calc u * (t * u') = (u * t) * u' := by group
      _ = (t * u) * u' := by rw [← h1]
      _ = t * (u * u') := by group
      _ = t * (u' * u) := by rw [hc]
      _ = (t * u') * u := by group
  · rw [hau, hbu]
    calc (t * u) * u' = t * (u * u') := by group
      _ = t * (u' * u) := by rw [hc]
      _ = (t * u') * u := by group
      _ = (u' * t) * u := by rw [h2]
      _ = u' * (t * u) := by group
  · rw [hau, hbu]
    have e1 : (t * u) * (t * u') = u * u' := by
      calc (t * u) * (t * u') = t * (u * t) * u' := by group
        _ = t * (t * u) * u' := by rw [← h1]
        _ = (t * t) * (u * u') := by group
        _ = u * u' := by rw [htt, one_mul]
    have e2 : (t * u') * (t * u) = u' * u := by
      calc (t * u') * (t * u) = t * (u' * t) * u := by group
        _ = t * (t * u') * u := by rw [← h2]
        _ = (t * t) * (u' * u) := by group
        _ = u' * u := by rw [htt, one_mul]
    rw [e1, e2, hc]

theorem inf_zpowers_invol_eq_bot (htt : t * t = 1) (htnU : t ∉ U) : U ⊓ zpowers t = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyU, hyt⟩ := Subgroup.mem_inf.1 hy
  rcases eq_one_or_eq_of_mem_zpowers_invol htt hyt with h | h
  · rw [Subgroup.mem_bot]
    exact h
  · exact absurd (h ▸ hyU) htnU

theorem card_zpowers_invol (htt : t * t = 1) (htnU : t ∉ U) : Nat.card (zpowers t) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht1 : t ≠ 1 := fun h => htnU (h ▸ U.one_mem)
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  rw [Nat.card_zpowers, hord]

theorem card_U0 (hF : IsF20 U x v) (htt : t * t = 1) (htU : ∀ u ∈ U, t * u = u * t) (htnU : t ∉ U) :
    Nat.card ↥(U ⊔ zpowers t : Subgroup Γ) = 32 := by
  have hnorm : zpowers t ≤ normalizer (U : Set Γ) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_of_comm htU
  rw [card_sup_of_inf_eq_bot' hnorm (inf_zpowers_invol_eq_bot htt htnU), hF.card,
    card_zpowers_invol htt htnU]

theorem isPGroup_U0 (hF : IsF20 U x v) (htt : t * t = 1) (htU : ∀ u ∈ U, t * u = u * t) (htnU : t ∉ U) :
    IsPGroup 2 ↥(U ⊔ zpowers t : Subgroup Γ) :=
  IsPGroup.of_card (n := 5) (by rw [card_U0 hF htt htU htnU]; norm_num)

@[expose] def deltaSet (U : Subgroup Γ) (t : Γ) : Set Γ := (fun u => t * u) '' (U : Set Γ)

theorem card_deltaSet (hF : IsF20 U x v) (t : Γ) : Nat.card ↥(deltaSet U t) = 16 := by
  rw [deltaSet, Nat.card_image_of_injective (mul_right_injective t) (U : Set Γ)]
  exact hF.card

@[expose, instance_reducible] def conjSetAction (K : Subgroup Γ) (Δ : Set Γ) (h : ∀ k ∈ K, ∀ δ ∈ Δ, k * δ * k⁻¹ ∈ Δ) :
    MulAction ↥K ↥Δ where
  smul k δ := ⟨(k : Γ) * (δ : Γ) * (k : Γ)⁻¹, h k k.2 δ δ.2⟩
  one_smul δ := Subtype.ext (by
    show ((1 : ↥K) : Γ) * (δ : Γ) * ((1 : ↥K) : Γ)⁻¹ = δ
    simp)
  mul_smul a b δ := Subtype.ext (by
    show ((a * b : ↥K) : Γ) * (δ : Γ) * ((a * b : ↥K) : Γ)⁻¹ =
      (a : Γ) * ((b : Γ) * (δ : Γ) * (b : Γ)⁻¹) * (a : Γ)⁻¹
    simp [mul_assoc])

theorem exists_zpow_mul_of_mem_sup {P : Subgroup Γ} (htP : ∀ p ∈ P, t * p = p * t) {k : Γ}
    (hk : k ∈ zpowers t ⊔ P) : ∃ a : ℤ, ∃ p ∈ P, k = t ^ a * p := by
  have hnorm : zpowers t ≤ normalizer (P : Set Γ) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_of_comm htP
  have hset : (zpowers t : Set Γ) * (P : Set Γ) = ((zpowers t ⊔ P : Subgroup Γ) : Set Γ) :=
    (Subgroup.coe_mul_of_left_le_normalizer_right (zpowers t) P hnorm).symm
  have hk' : k ∈ (zpowers t : Set Γ) * (P : Set Γ) := by rw [hset]; exact hk
  obtain ⟨a, ha, p, hp, hkp⟩ := hk'
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  exact ⟨n, p, hp, hkp.symm⟩

theorem comm_of_mem_sup_zpowers_left {P : Subgroup Γ} (htP : ∀ p ∈ P, t * p = p * t) {k : Γ}
    (hk : k ∈ zpowers t ⊔ P) : k * t = t * k := by
  obtain ⟨a, p, hp, rfl⟩ := exists_zpow_mul_of_mem_sup htP hk
  have h1 : t ^ a * t = t * t ^ a := (Commute.zpow_left (Commute.refl t) a).eq
  calc t ^ a * p * t = t ^ a * (p * t) := by group
    _ = t ^ a * (t * p) := by rw [htP p hp]
    _ = (t ^ a * t) * p := by group
    _ = (t * t ^ a) * p := by rw [h1]
    _ = t * (t ^ a * p) := by group

theorem Pgrp_conj_x_mem (hF : IsF20 U x v) {p : Γ} (hp : p ∈ Pgrp U x v) :
    p * x * p⁻¹ ∈ zpowers x ⊔ U := by
  obtain ⟨w, hw, hwv⟩ := hF.exists_frob
  have hvx : v ∈ normalizer (zpowers x : Set Γ) := hw.zpowers_y_le_normalizer (hwv ▸ mem_zpowers v)
  have hA : Pgrp U x v ≤ normalizer ((zpowers x ⊔ U : Subgroup Γ) : Set Γ) := by
    refine sup_le ?_ (sup_le ?_ ?_)
    · exact (le_sup_right : U ≤ zpowers x ⊔ U).trans Subgroup.le_normalizer
    · rw [Subgroup.zpowers_le]
      exact Subgroup.le_normalizer (mem_sup_left (mem_zpowers x))
    · rw [Subgroup.zpowers_le]
      exact mem_normalizer_sup' hvx hF.v_norm
  exact (mem_normalizer_iff.1 (hA hp) x).1 (mem_sup_left (mem_zpowers x))

theorem mem_sup_of_comm_mod (hF : IsF20 U x v) {U0 : Subgroup Γ} (hU0 : IsPGroup 2 U0) (hUU0 : U ≤ U0)
    {p : Γ} (hp : p ∈ Pgrp U x v) (hc : p * x * p⁻¹ * x⁻¹ ∈ U0) : p ∈ U ⊔ zpowers x := by
  obtain ⟨u, hu, f, hf, rfl⟩ := hF.exists_mul hp
  obtain ⟨w, hw, hwv⟩ := hF.exists_frob
  have hfF : f ∈ (zpowers x ⊔ zpowers w : Subgroup Γ) := by rw [hwv]; exact hf
  have hfx : f * x * f⁻¹ ∈ zpowers x :=
    (mem_normalizer_iff.1 (hw.sup_le_normalizer hfF) x).1 (mem_zpowers x)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hfx
  have hxm : x ^ m ∈ normalizer (U : Set Γ) := zpow_mem hF.x_norm m
  have hy : u * (x ^ m * u⁻¹ * (x ^ m)⁻¹) ∈ U :=
    U.mul_mem hu ((mem_normalizer_iff.1 hxm u⁻¹).1 (U.inv_mem hu))
  have hc' : (u * (x ^ m * u⁻¹ * (x ^ m)⁻¹)) * (x ^ m * x⁻¹) ∈ U0 := by
    have e : (u * (x ^ m * u⁻¹ * (x ^ m)⁻¹)) * (x ^ m * x⁻¹) = u * f * x * (u * f)⁻¹ * x⁻¹ := by
      calc (u * (x ^ m * u⁻¹ * (x ^ m)⁻¹)) * (x ^ m * x⁻¹)
          = u * x ^ m * u⁻¹ * x⁻¹ := by group
        _ = u * (f * x * f⁻¹) * u⁻¹ * x⁻¹ := by rw [hm]
        _ = u * f * x * (u * f)⁻¹ * x⁻¹ := by group
    rw [e]
    exact hc
  have hxmx : x ^ m * x⁻¹ ∈ U0 := by
    have h1 := U0.mul_mem (U0.inv_mem (hUU0 hy)) hc'
    rwa [inv_mul_cancel_left] at h1
  have hxmx1 : x ^ m * x⁻¹ = 1 := by
    refine eq_one_of_mem_zpowers_of_isPGroup_two hU0 hF.x5 hxmx ?_
    have : x ^ m * x⁻¹ = x ^ (m - 1) := by rw [zpow_sub_one]
    rw [this]
    exact zpow_mem (mem_zpowers x) _
  have hxx : f * x * f⁻¹ = x := by
    rw [← hm]
    have : x ^ m = x := by
      have h2 : x ^ m * x⁻¹ * x = 1 * x := by rw [hxmx1]
      simpa using h2
    exact this
  have hfc : f * x = x * f := by
    have := hxx
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hfx' : f ∈ zpowers x := hw.mem_zpowers_of_comm hfF hfc
  exact mul_mem (mem_sup_left hu) (mem_sup_right hfx')

theorem mem_sup_subgroupOf_of_coe {K : Subgroup Γ} (hxK : x ∈ K) {A : Subgroup Γ} (hAK : A ≤ K)
    (hx : x ∈ normalizer (A : Set Γ)) {y : ↥K} (hy : (y : Γ) ∈ zpowers x ⊔ A) :
    y ∈ zpowers (⟨x, hxK⟩ : ↥K) ⊔ A.subgroupOf K := by
  have hnorm : zpowers x ≤ normalizer (A : Set Γ) := by
    rw [Subgroup.zpowers_le]
    exact hx
  have hset : (zpowers x : Set Γ) * (A : Set Γ) = ((zpowers x ⊔ A : Subgroup Γ) : Set Γ) :=
    (Subgroup.coe_mul_of_left_le_normalizer_right (zpowers x) A hnorm).symm
  have hy' : (y : Γ) ∈ (zpowers x : Set Γ) * (A : Set Γ) := by rw [hset]; exact hy
  obtain ⟨a, ha, b, hb, hab⟩ := hy'
  have hab' : a * b = (y : Γ) := hab
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have hyeq : y = (⟨x, hxK⟩ : ↥K) ^ n * ⟨b, hAK hb⟩ := Subtype.ext (by rw [← hab']; simp)
  rw [hyeq]
  exact mul_mem (mem_sup_left (Subgroup.zpow_mem_zpowers _ n))
    (mem_sup_right (Subgroup.mem_subgroupOf.2 hb))

theorem card_zpowers_sup_Pgrp (hF : IsF20 U x v) (htt : t * t = 1) (htnU : t ∉ U)
    (htP : ∀ p ∈ Pgrp U x v, t * p = p * t) (htPbot : zpowers t ⊓ Pgrp U x v = ⊥) :
    Nat.card ↥(zpowers t ⊔ Pgrp U x v : Subgroup Γ) = 640 := by
  have hnormtP : zpowers t ≤ normalizer ((Pgrp U x v : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_of_comm htP
  rw [sup_comm, card_sup_of_inf_eq_bot' hnormtP (by rw [inf_comm]; exact htPbot), card_Pgrp hF,
    card_zpowers_invol htt htnU]

theorem exists_W0 [Finite Γ] (hF : IsF20 U x v) {K : Subgroup Γ}
    (htt : t * t = 1) (htU : ∀ u ∈ U, t * u = u * t) (htnU : t ∉ U)
    (hUK : U ≤ K) (htK : t ∈ K) (hPK : Pgrp U x v ≤ K)
    (htP : ∀ p ∈ Pgrp U x v, t * p = p * t) (htPbot : zpowers t ⊓ Pgrp U x v = ⊥)
    (hKU0 : ∀ k ∈ K, k ∈ normalizer ((U ⊔ zpowers t : Subgroup Γ) : Set Γ))
    (hΔ : ∀ k ∈ K, ∀ u ∈ U, ∃ u' ∈ U, k * (t * u) * k⁻¹ = t * u')
    (htr : ∀ u ∈ U, ∃ k ∈ K, k * t * k⁻¹ = t * u)
    (hC : ∀ k ∈ K, k * t = t * k → k ∈ zpowers t ⊔ Pgrp U x v) :
    Nat.card K = 16 * 640 ∧ ∃ W : Subgroup Γ, W ≤ K ∧ (∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W) ∧
      IsPGroup 2 W ∧ U ⊔ zpowers t ≤ W ∧ Nat.card W = 512 ∧
      (∀ a ∈ W, ∀ b ∈ W, a * b * a⁻¹ * b⁻¹ ∈ U ⊔ zpowers t) ∧ (∀ a ∈ W, a * a ∈ U ⊔ zpowers t) ∧
      (∀ w ∈ W, w * t = t * w → w ∈ U ⊔ zpowers t) ∧ (∀ u ∈ U, ∃ w ∈ W, w * t * w⁻¹ = t * u) ∧
      (∀ M : Subgroup Γ, M ≤ K → (∀ k ∈ K, ∀ m ∈ M, k * m * k⁻¹ ∈ M) → IsPGroup 2 M → M ≤ W) := by
  classical
  have hU0K : U ⊔ zpowers t ≤ K := sup_le hUK (zpowers_le.2 htK)
  have hU0card : Nat.card ↥(U ⊔ zpowers t) = 32 := card_U0 hF htt htU htnU
  have hU02 : IsPGroup 2 ↥(U ⊔ zpowers t) := isPGroup_U0 hF htt htU htnU
  have hxP : x ∈ Pgrp U x v := mem_sup_right (mem_sup_left (mem_zpowers x))
  have hxK : x ∈ K := hPK hxP
  have htU0 : t ∈ U ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have hUU0 : U ≤ U ⊔ zpowers t := le_sup_left
  have hdel : ∀ k ∈ K, ∀ δ ∈ deltaSet U t, k * δ * k⁻¹ ∈ deltaSet U t := by
    rintro k hk _ ⟨u, hu, rfl⟩
    obtain ⟨u', hu', h⟩ := hΔ k hk u hu
    exact ⟨u', hu', h.symm⟩
  letI : MulAction ↥K ↥(deltaSet U t) := conjSetAction K (deltaSet U t) hdel
  have hsmul : ∀ (k : ↥K) (δ : ↥(deltaSet U t)),
      ((k • δ : ↥(deltaSet U t)) : Γ) = (k : Γ) * (δ : Γ) * (k : Γ)⁻¹ := fun k δ => rfl
  let ω : ↥(deltaSet U t) := ⟨t, 1, U.one_mem, mul_one t⟩
  have hω : (ω : Γ) = t := rfl
  haveI : MulAction.IsPretransitive ↥K ↥(deltaSet U t) := by
    have key : ∀ δ : ↥(deltaSet U t), ∃ k : ↥K, k • ω = δ := by
      rintro ⟨_, u, hu, rfl⟩
      obtain ⟨k, hk, hkt⟩ := htr u hu
      exact ⟨⟨k, hk⟩, Subtype.ext (by rw [hsmul, hω]; exact hkt)⟩
    refine ⟨fun α β => ?_⟩
    obtain ⟨a, ha⟩ := key α
    obtain ⟨b, hb⟩ := key β
    refine ⟨b * a⁻¹, ?_⟩
    calc (b * a⁻¹) • α = (b * a⁻¹) • (a • ω) := by rw [ha]
      _ = (b * a⁻¹ * a) • ω := (mul_smul _ _ _).symm
      _ = b • ω := by rw [inv_mul_cancel_right]
      _ = β := hb
  have hnormtP : zpowers t ≤ normalizer ((Pgrp U x v : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_of_comm htP
  have hN : ∀ k : ↥K, k ∈ (U ⊔ zpowers t).subgroupOf K ↔ ∀ δ : ↥(deltaSet U t), k • δ = δ := by
    intro k
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hk δ
      obtain ⟨val, u, hu, hδ⟩ := δ
      apply Subtype.ext
      rw [hsmul]
      show (k : Γ) * val * (k : Γ)⁻¹ = val
      have hval : val = t * u := hδ.symm
      have hvalU0 : val ∈ U ⊔ zpowers t := by rw [hval]; exact mul_mem htU0 (hUU0 hu)
      have hc := comm_of_mem_sup_zpowers hF htt htU hk hvalU0
      rw [hc]
      group
    · intro h
      have h1 : (k : Γ) * t * (k : Γ)⁻¹ = t := by
        have := congrArg Subtype.val (h ω)
        rw [hsmul] at this
        exact this
      have h2 : ∀ u ∈ U, (k : Γ) * u * (k : Γ)⁻¹ = u := by
        intro u hu
        have this := congrArg Subtype.val (h ⟨t * u, u, hu, rfl⟩)
        rw [hsmul] at this
        have this' : (k : Γ) * (t * u) * (k : Γ)⁻¹ = t * u := this
        have e : (k : Γ) * (t * u) * (k : Γ)⁻¹ =
            ((k : Γ) * t * (k : Γ)⁻¹) * ((k : Γ) * u * (k : Γ)⁻¹) := by group
        rw [e, h1] at this'
        exact mul_left_cancel this'
      have hkt : (k : Γ) * t = t * k := by
        rw [mul_inv_eq_iff_eq_mul] at h1
        exact h1
      obtain ⟨a, p, hp, hkp⟩ := exists_zpow_mul_of_mem_sup htP (hC k k.2 hkt)
      have hta : ∀ u ∈ U, t ^ a * u = u * t ^ a := fun u hu =>
        (Commute.zpow_left (show Commute t u from htU u hu) a).eq
      have hpc : ∀ u ∈ U, p * u = u * p := by
        intro u hu
        have hk2 : (k : Γ) * u = u * k := by
          have := h2 u hu
          rw [mul_inv_eq_iff_eq_mul] at this
          exact this
        rw [hkp] at hk2
        have h3 : t ^ a * (p * u) = t ^ a * (u * p) := by
          calc t ^ a * (p * u) = t ^ a * p * u := by group
            _ = u * (t ^ a * p) := hk2
            _ = (u * t ^ a) * p := by group
            _ = (t ^ a * u) * p := by rw [hta u hu]
            _ = t ^ a * (u * p) := by group
        exact mul_left_cancel h3
      have hpU : p ∈ U := centralizer_Pgrp hF hp hpc
      rw [hkp]
      exact mul_mem (mem_sup_right (Subgroup.zpow_mem_zpowers t a)) (mem_sup_left hpU)
  have hstab : MulAction.stabilizer ↥K ω = (zpowers t ⊔ Pgrp U x v).subgroupOf K := by
    ext k
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : (k : Γ) * t * (k : Γ)⁻¹ = t := by
        have := congrArg Subtype.val h
        rw [hsmul] at this
        exact this
      have hkt : (k : Γ) * t = t * k := by
        rw [mul_inv_eq_iff_eq_mul] at h1
        exact h1
      exact hC k k.2 hkt
    · intro h
      apply Subtype.ext
      rw [hsmul]
      show (k : Γ) * t * (k : Γ)⁻¹ = t
      rw [comm_of_mem_sup_zpowers_left htP h]
      group
  have hle : zpowers t ⊔ Pgrp U x v ≤ K := sup_le (zpowers_le.2 htK) hPK
  have hcardCt : Nat.card ↥(zpowers t ⊔ Pgrp U x v : Subgroup Γ) = 640 :=
    card_zpowers_sup_Pgrp hF htt htnU htP htPbot
  have hcardN : Nat.card ↥((U ⊔ zpowers t).subgroupOf K) = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU0K).toEquiv, hU0card]
  have hS : Nat.card ↥(MulAction.stabilizer ↥K ω) = 20 * Nat.card ↥((U ⊔ zpowers t).subgroupOf K) := by
    rw [hstab, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcardCt, hcardN]
  have hcardΩ : Nat.card ↥(deltaSet U t) = 16 := card_deltaSet hF t
  have hdec : ∀ g ∈ zpowers t ⊔ Pgrp U x v, ∃ a : ℤ, ∃ p ∈ Pgrp U x v,
      g = t ^ a * p ∧ g * x * g⁻¹ = p * x * p⁻¹ := by
    intro g hg
    obtain ⟨a, p, hp, hgp⟩ := exists_zpow_mul_of_mem_sup htP hg
    refine ⟨a, p, hp, hgp, ?_⟩
    have hpxP : p * x * p⁻¹ ∈ Pgrp U x v := mul_mem (mul_mem hp hxP) (inv_mem hp)
    have hc : t ^ a * (p * x * p⁻¹) = (p * x * p⁻¹) * t ^ a :=
      (Commute.zpow_left (show Commute t (p * x * p⁻¹) from htP _ hpxP) a).eq
    rw [hgp]
    calc t ^ a * p * x * (t ^ a * p)⁻¹ = (t ^ a * (p * x * p⁻¹)) * (t ^ a)⁻¹ := by group
      _ = ((p * x * p⁻¹) * t ^ a) * (t ^ a)⁻¹ := by rw [hc]
      _ = p * x * p⁻¹ := by group
  let xK : ↥K := ⟨x, hxK⟩
  have hx5 : xK ^ 5 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact hF.x5)
  have hxω : xK • ω = ω := by
    apply Subtype.ext
    rw [hsmul, hω]
    show x * t * x⁻¹ = t
    rw [← htP x hxP]
    group
  have hfix : ∀ α : ↥(deltaSet U t), xK • α = α → α = ω := by
    rintro ⟨_, u, hu, rfl⟩ h
    have h1 := congrArg Subtype.val h
    rw [hsmul] at h1
    have h1' : x * (t * u) * x⁻¹ = t * u := h1
    have hxu : x * u * x⁻¹ = u := by
      have e : x * (t * u) * x⁻¹ = t * (x * u * x⁻¹) := by
        calc x * (t * u) * x⁻¹ = (x * t) * u * x⁻¹ := by group
          _ = (t * x) * u * x⁻¹ := by rw [← htP x hxP]
          _ = t * (x * u * x⁻¹) := by group
      rw [e] at h1'
      exact mul_left_cancel h1'
    have hu1 : u = 1 := hF.fpf u hu hxu
    apply Subtype.ext
    show t * u = t
    rw [hu1, mul_one]
  have hnorm : ∀ g ∈ MulAction.stabilizer ↥K ω,
      g * xK * g⁻¹ ∈ zpowers xK ⊔ (U ⊔ zpowers t).subgroupOf K := by
    intro g hg
    rw [hstab, Subgroup.mem_subgroupOf] at hg
    obtain ⟨a, p, hp, hgp, hgx⟩ := hdec _ hg
    have hpx : p * x * p⁻¹ ∈ zpowers x ⊔ U := Pgrp_conj_x_mem hF hp
    apply mem_sup_subgroupOf_of_coe hxK hU0K (hKU0 x hxK)
    show (g : Γ) * x * (g : Γ)⁻¹ ∈ zpowers x ⊔ (U ⊔ zpowers t)
    rw [hgx]
    exact sup_le_sup_left hUU0 _ hpx
  have hcent : ∀ g ∈ MulAction.stabilizer ↥K ω,
      g * xK * g⁻¹ * xK⁻¹ ∈ (U ⊔ zpowers t).subgroupOf K →
        g ∈ zpowers xK ⊔ (U ⊔ zpowers t).subgroupOf K := by
    intro g hg hgc
    rw [hstab, Subgroup.mem_subgroupOf] at hg
    rw [Subgroup.mem_subgroupOf] at hgc
    obtain ⟨a, p, hp, hgp, hgx⟩ := hdec _ hg
    have hgc' : (g : Γ) * x * (g : Γ)⁻¹ * x⁻¹ ∈ U ⊔ zpowers t := hgc
    rw [hgx] at hgc'
    have hpUx : p ∈ U ⊔ zpowers x := mem_sup_of_comm_mod hF hU02 hUU0 hp hgc'
    apply mem_sup_subgroupOf_of_coe hxK hU0K (hKU0 x hxK)
    show (g : Γ) ∈ zpowers x ⊔ (U ⊔ zpowers t)
    rw [hgp]
    refine mul_mem (mem_sup_right (mem_sup_right (Subgroup.zpow_mem_zpowers t a))) ?_
    have : U ⊔ zpowers x ≤ zpowers x ⊔ (U ⊔ zpowers t) :=
      sup_le (hUU0.trans le_sup_right) le_sup_left
    exact this hpUx
  have hN2 : IsPGroup 2 ↥((U ⊔ zpowers t).subgroupOf K) :=
    IsPGroup.of_card (n := 5) (by rw [hcardN]; norm_num)
  obtain ⟨W, hWn, hW2, hNW, hWc, hWcomm, hWsq, hWtr, hWreg, hWmax⟩ :=
    exists_regular_normal_two_of_action hcardΩ ω hN hN2 hS hx5 hxω hfix hnorm hcent
  have hKcard : Nat.card ↥K = 16 * 640 := by
    have h1 : Nat.card ↥(MulAction.stabilizer ↥K ω) * Nat.card ↥(deltaSet U t) = Nat.card ↥K := by
      rw [← MulAction.index_stabilizer_of_transitive ↥K ω]
      exact Subgroup.card_mul_index _
    rw [hS, hcardN, hcardΩ] at h1
    omega
  refine ⟨hKcard, W.map K.subtype, Subgroup.map_subtype_le W, ?_, hW2.map K.subtype, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rintro k hk _ ⟨w, hw, rfl⟩
    exact ⟨⟨k, hk⟩ * w * ⟨k, hk⟩⁻¹, hWn.conj_mem w hw ⟨k, hk⟩, rfl⟩
  · intro y hy
    exact ⟨⟨y, hU0K hy⟩, hNW (Subgroup.mem_subgroupOf.2 hy), rfl⟩
  · rw [Subgroup.card_map_of_injective K.subtype_injective, hWc, hcardN]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hWcomm a ha b hb)
  · rintro _ ⟨a, ha, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hWsq a ha)
  · rintro _ ⟨w, hw, rfl⟩ hwt
    have hwω : w • ω = ω := by
      apply Subtype.ext
      rw [hsmul, hω]
      show (w : Γ) * t * (w : Γ)⁻¹ = t
      have hwt' : (w : Γ) * t = t * (w : Γ) := hwt
      rw [hwt']
      group
    exact Subgroup.mem_subgroupOf.1 (hWreg w hw hwω)
  · intro u hu
    obtain ⟨w, hw, hwω⟩ := hWtr ω ⟨t * u, u, hu, rfl⟩
    refine ⟨w, ⟨w, hw, rfl⟩, ?_⟩
    have := congrArg Subtype.val hwω
    rw [hsmul, hω] at this
    exact this
  · intro M hMK hMst hM2
    intro m hm
    have hmK : m ∈ K := hMK hm
    have hMn : (M.subgroupOf K).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hMst g g.2 n hn⟩
    have hMp : IsPGroup 2 ↥(M.subgroupOf K) := hM2.comap_subtype
    have hmW := hWmax _ hMn hMp (Subgroup.mem_subgroupOf.2 hm : (⟨m, hmK⟩ : ↥K) ∈ M.subgroupOf K)
    exact ⟨⟨m, hmK⟩, hmW, rfl⟩

end K6

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
