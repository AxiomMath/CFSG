module

import CFSG.Walter.AStar.Subnormal
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.AGLEmbedding.SPLMSide

open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_zpowers_of_pow {p : ℕ} {u : G} (hu : ∃ k : ℕ, u ^ p ^ k = 1) :
    IsPGroup p (zpowers u) := by
  obtain ⟨k, hk⟩ := hu
  rintro ⟨x, n, rfl⟩
  refine ⟨k, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]

theorem exists_sylow_normalizerMonoidHom_mem {p : ℕ} [Fact p.Prime] {Λ : Subgroup G}
    (hΛ : Λ.IsSubnormal) {u : G} (hu : u ∈ Subgroup.normalizer (Λ : Set G))
    (hup : ∃ k : ℕ, u ^ p ^ k = 1) :
    ∃ S : Sylow p Λ, ∀ x ∈ (S : Subgroup Λ),
      Λ.normalizerMonoidHom ⟨u, hu⟩ x ∈ (S : Subgroup Λ) := by
  classical
  obtain ⟨R, hR⟩ := (isPGroup_zpowers_of_pow hup).exists_le_sylow
  have huR : u ∈ (R : Subgroup G) := hR (mem_zpowers u)
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal R hΛ
  have hmemP : ∀ k : Λ, k ∈ (P : Subgroup Λ) ↔ (k : G) ∈ (R : Subgroup G) := by
    intro k
    constructor
    · intro hk
      have : (k : G) ∈ (P : Subgroup Λ).map Λ.subtype := ⟨k, hk, rfl⟩
      rw [hP] at this
      exact this.1
    · intro hk
      have : (k : G) ∈ (R : Subgroup G) ⊓ Λ := ⟨hk, k.2⟩
      rw [← hP] at this
      obtain ⟨k', hk', hkk'⟩ := this
      have : k' = k := Subtype.ext hkk'
      rwa [← this]
  refine ⟨P, fun x hx => ?_⟩
  rw [hmemP]
  exact R.mul_mem (R.mul_mem huR ((hmemP x).mp hx)) (R.inv_mem huR)

theorem exists_mem_fixed_mod_center {Λ : Type} [Group Λ] [Finite Λ] {p : ℕ} [hp : Fact p.Prime]
    (S : Subgroup Λ) (hSp : IsPGroup p S) (hSZ : ¬ S ≤ Subgroup.center Λ) (α : MulAut Λ)
    {k : ℕ} (hαk : ∀ x : Λ, (α ^ (p ^ k)) x = x) (hαS : ∀ x ∈ S, α x ∈ S) :
    ∃ s ∈ S, s ∉ Subgroup.center Λ ∧ s⁻¹ * α s ∈ Subgroup.center Λ := by
  classical
  set N' : Subgroup S := (Subgroup.center Λ).subgroupOf S with hN'
  have hN'n : N'.Normal := ⟨fun n hn g => by
    rw [hN', Subgroup.mem_subgroupOf] at hn ⊢
    have : ((g * n * g⁻¹ : S) : Λ) = (n : Λ) := by
      show (g : Λ) * n * (g : Λ)⁻¹ = n
      rw [Subgroup.mem_center_iff.mp hn (g : Λ)]
      group
    rw [this]; exact hn⟩
  let αS : S → S := fun s => ⟨α s, hαS s s.2⟩
  have hαSrel : ∀ a b : S, a⁻¹ * b ∈ N' → (αS a)⁻¹ * αS b ∈ N' := by
    intro a b hab
    rw [hN', Subgroup.mem_subgroupOf] at hab ⊢
    have : (((αS a)⁻¹ * αS b : S) : Λ) = α ((a : Λ)⁻¹ * b) := by
      show (α a)⁻¹ * α b = _
      rw [map_mul, map_inv]
    have hab' : (a : Λ)⁻¹ * b ∈ Subgroup.center Λ := by simpa using hab
    rw [this]
    exact MulEquivClass.apply_mem_center α hab'
  let f : Function.End (S ⧸ N') :=
    Quotient.map' αS (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      exact hαSrel a b hab)
  have hαSn : ∀ n : ℕ, ∀ s : S, (((αS^[n]) s : S) : Λ) = (α ^ n) s := by
    intro n
    induction n with
    | zero => intro s; rfl
    | succ n ih =>
      intro s
      rw [Function.iterate_succ_apply', pow_succ', MulAut.mul_apply, ← ih s]
  have hfn : ∀ n : ℕ, ∀ s : S, (f ^ n) (s : S ⧸ N') = ((αS^[n]) s : S ⧸ N') := by
    intro n
    induction n with
    | zero => intro s; rfl
    | succ n ih =>
      intro s
      rw [pow_succ', Function.iterate_succ_apply']
      show f ((f ^ n) (s : S ⧸ N')) = _
      rw [ih s]
      rfl
  have hfp : f ^ p ^ k = 1 := by
    funext x
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hfn]
    have : (αS^[p ^ k]) s = s := Subtype.ext (by rw [hαSn, hαk])
    rw [this]
    rfl
  have : Fintype (S ⧸ N') := Fintype.ofFinite _
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) hfp
  obtain ⟨m, hm⟩ := hSp.index N'
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.index_eq_one] at hm
    apply hSZ
    intro x hx
    have : (⟨x, hx⟩ : S) ∈ N' := by rw [hm]; trivial
    rw [hN', Subgroup.mem_subgroupOf] at this
    exact this
  have hcard : Fintype.card (S ⧸ N') = p ^ m := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hm]
  have h1fix : f (1 : S ⧸ N') = 1 := by
    show ((αS 1 : S) : S ⧸ N') = ((1 : S) : S ⧸ N')
    congr 1
    exact Subtype.ext (map_one α)
  obtain ⟨x, hxf, hx1⟩ : ∃ x : S ⧸ N', f x = x ∧ x ≠ 1 := by
    by_contra hno
    push Not at hno
    have hone : Fintype.card (Function.fixedPoints f) = 1 := by
      rw [Fintype.card_eq_one_iff]
      refine ⟨⟨1, h1fix⟩, fun y => Subtype.ext (hno y.1 y.2)⟩
    rw [hone, hcard] at hmod
    have h0 : p ^ m % p = 0 := by
      obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      rw [pow_succ, Nat.mul_mod_left]
    have h1p : 1 % p = 1 := Nat.mod_eq_of_lt hp.out.one_lt
    have := hmod.symm
    rw [Nat.ModEq, h0, h1p] at this
    exact one_ne_zero this
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
  have hsZ : (s : Λ) ∉ Subgroup.center Λ := by
    intro h
    apply hx1
    rw [QuotientGroup.eq_one_iff, hN', Subgroup.mem_subgroupOf]
    exact h
  have hsφ : (s : Λ)⁻¹ * α s ∈ Subgroup.center Λ := by
    have h2 : ((αS s : S) : S ⧸ N') = (s : S ⧸ N') := hxf
    rw [QuotientGroup.eq, hN', Subgroup.mem_subgroupOf] at h2
    have h3 := Subgroup.inv_mem _ h2
    have : (((αS s)⁻¹ * s : S) : Λ)⁻¹ = (s : Λ)⁻¹ * α s := by
      show ((α s)⁻¹ * s)⁻¹ = _
      group
    rw [this] at h3
    exact h3
  exact ⟨s, s.2, hsZ, hsφ⟩

theorem exists_pow_mem_center {Λ : Type} [Group Λ] {p : ℕ} [Fact p.Prime] (α : MulAut Λ)
    {s : Λ} (hs : ∃ m : ℕ, s ^ p ^ m = 1) (hsZ : s ∉ Subgroup.center Λ)
    (hsα : s⁻¹ * α s ∈ Subgroup.center Λ) :
    ∃ y : Λ, y ∉ Subgroup.center Λ ∧ (∃ k : ℕ, y ^ p ^ k = 1) ∧ y ^ p ∈ Subgroup.center Λ ∧
      y⁻¹ * α y ∈ Subgroup.center Λ := by
  classical
  obtain ⟨m₁, hsm₁⟩ := hs
  have hex : ∃ j : ℕ, s ^ p ^ j ∈ Subgroup.center Λ := ⟨m₁, by rw [hsm₁]; exact one_mem _⟩
  set j₀ := Nat.find hex with hj₀
  have hj₀mem : s ^ p ^ j₀ ∈ Subgroup.center Λ := Nat.find_spec hex
  have hj₀0 : j₀ ≠ 0 := by
    intro h
    rw [h, pow_zero, pow_one] at hj₀mem
    exact hsZ hj₀mem
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j₀ = j + 1 := ⟨j₀ - 1, by omega⟩
  have hjmin : ¬ s ^ p ^ j ∈ Subgroup.center Λ :=
    Nat.find_min hex (by rw [← hj₀, hj]; exact Nat.lt_succ_self j)
  have hmem' : s ^ p ^ (j + 1) ∈ Subgroup.center Λ := by rw [← hj]; exact hj₀mem
  set φ : Λ := s⁻¹ * α s with hφ
  have hαs : α s = s * φ := by rw [hφ]; group
  have hcomm : Commute s φ := Subgroup.mem_center_iff.mp hsα s
  refine ⟨s ^ p ^ j, hjmin, ⟨m₁, ?_⟩, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hsm₁, one_pow]
  · rw [← pow_mul, ← pow_succ]
    exact hmem'
  · rw [map_pow, hαs, hcomm.mul_pow, ← mul_assoc, inv_mul_cancel, one_mul]
    exact pow_mem hsα _

theorem exists_pelem_mod_center {p : ℕ} [hp : Fact p.Prime] {Λ : Subgroup G}
    (hΛ : Λ.IsSubnormal) {u : G} (hu : u ∈ Subgroup.normalizer (Λ : Set G))
    (hup : ∃ k : ℕ, u ^ p ^ k = 1) (hpZ : p ∣ (Subgroup.center Λ).index) :
    ∃ y : Λ, y ∉ Subgroup.center Λ ∧ (∃ k : ℕ, y ^ p ^ k = 1) ∧
      y ^ p ∈ Subgroup.center Λ ∧
      y⁻¹ * ⟨u * (y : G) * u⁻¹, (Subgroup.mem_normalizer_iff.mp hu y).mp y.2⟩ ∈
        Subgroup.center Λ := by
  obtain ⟨S, hS⟩ := exists_sylow_normalizerMonoidHom_mem hΛ hu hup
  let α : MulAut Λ := Λ.normalizerMonoidHom ⟨u, hu⟩
  have hαeq : ∀ k : Λ, α k = ⟨u * (k : G) * u⁻¹, (Subgroup.mem_normalizer_iff.mp hu k).mp k.2⟩ :=
    fun k => Subtype.ext rfl
  obtain ⟨k, hk⟩ := hup
  have hαk : ∀ x : Λ, (α ^ (p ^ k)) x = x := by
    intro x
    have h1 : α ^ (p ^ k) = Λ.normalizerMonoidHom (⟨u, hu⟩ ^ (p ^ k)) := by rw [map_pow]
    have h2 : (⟨u, hu⟩ : Subgroup.normalizer (Λ : Set G)) ^ (p ^ k) = 1 := Subtype.ext hk
    rw [h1, h2, map_one]
    rfl
  have hSZ : ¬ (S : Subgroup Λ) ≤ Subgroup.center Λ := fun hle =>
    S.not_dvd_index (dvd_trans hpZ (Subgroup.index_dvd_of_le hle))
  obtain ⟨s, hsS, hsZ, hsα⟩ := exists_mem_fixed_mod_center (S : Subgroup Λ) S.isPGroup' hSZ α
    hαk hS
  have hs : ∃ m : ℕ, s ^ p ^ m = 1 := by
    obtain ⟨m, hm⟩ := S.isPGroup' ⟨s, hsS⟩
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  obtain ⟨y, hyZ, hyp, hyc, hyα⟩ := exists_pow_mem_center α hs hsZ hsα
  refine ⟨y, hyZ, hyp, hyc, ?_⟩
  rw [← hαeq]
  exact hyα

end CFSG.AGLEmbedding.SPLMSide
