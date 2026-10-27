module

public import CFSG.LinearAlgebra.IrreducibleBinaryCentralizerField
public import Mathlib.GroupTheory.PGroup

public noncomputable section

namespace CFSG.ComponentClassification.BMCase

open Subgroup Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem not_dvd_card_GL_of_three_le {d : ℕ} (hd : d ∣ 24) (h3 : 3 ≤ d) :
    ¬ 23 ∣ ∏ i : Fin (24 / d), ((2 ^ d) ^ (24 / d) - (2 ^ d) ^ (i : ℕ)) := by
  have hd' : d ≤ 24 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d <;> simp_all (config := {decide := true})

theorem pow_three_eq_one_of_orderOf_dvd {G : Type*} [Monoid G] {a : G} {d : ℕ} (hd : 0 < d)
    (hd2 : d ≤ 2) (ha : orderOf a ∣ 2 ^ d - 1) : a ^ 3 = 1 := by
  apply orderOf_dvd_iff_pow_eq_one.1
  interval_cases d
  · exact ha.trans (by norm_num)
  · exact ha

variable [FiniteDimensional (ZMod 2) V]

theorem pow_three_eq_one_of_dim_twentyfour (hV : finrank (ZMod 2) V = 24)
    (H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    (hirr : ∀ W : Submodule (ZMod 2) V,
      (∀ h ∈ H, ∀ w ∈ W, (h : V →ₗ[ZMod 2] V) w ∈ W) → W = ⊥ ∨ W = ⊤)
    (h23 : 23 ∣ Nat.card H) (a : LinearMap.GeneralLinearGroup (ZMod 2) V)
    (ha : a ∈ centralizer (H : Set (LinearMap.GeneralLinearGroup (ZMod 2) V))) : a ^ 3 = 1 := by
  obtain ⟨hR, d, hd0, hd, hcard, hord, hemb, -⟩ :=
    CFSG.LinearAlgebra.irreducible_binary_linear_centralizer_field_degree_bound (by norm_num) hV
      H hirr a ha
  refine pow_three_eq_one_of_orderOf_dvd hd0 ?_ hord
  by_contra hlt
  push Not at hlt
  let _ := hR.toField
  obtain ⟨φ, hφ⟩ := hemb
  have hdvd := Subgroup.card_dvd_of_injective φ hφ
  have : Finite (Algebra.adjoin (ZMod 2) {(a : Module.End (ZMod 2) V)}) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have : Fintype (Algebra.adjoin (ZMod 2) {(a : Module.End (ZMod 2) V)}) := Fintype.ofFinite _
  rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hcard] at hdvd
  exact not_dvd_card_GL_of_three_le hd hlt (h23.trans hdvd)

theorem finite_generalLinearGroup : Finite (LinearMap.GeneralLinearGroup (ZMod 2) V) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V →ₗ[ZMod 2] V) := Finite.of_injective _ DFunLike.coe_injective
  infer_instance

theorem pow_three_eq_one_of_dim_twentytwo (hV : finrank (ZMod 2) V = 22)
    (H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    (hirr : ∀ W : Submodule (ZMod 2) V,
      (∀ h ∈ H, ∀ w ∈ W, (h : V →ₗ[ZMod 2] V) w ∈ W) → W = ⊥ ∨ W = ⊤)
    (h2 : 2 ^ 18 ∣ Nat.card H) (a : LinearMap.GeneralLinearGroup (ZMod 2) V)
    (ha : a ∈ centralizer (H : Set (LinearMap.GeneralLinearGroup (ZMod 2) V))) : a ^ 3 = 1 := by
  obtain ⟨-, d, hd0, hd, -, hord, -, h2part⟩ :=
    CFSG.LinearAlgebra.irreducible_binary_linear_centralizer_field_degree_bound (by norm_num) hV
      H hirr a ha
  refine pow_three_eq_one_of_orderOf_dvd hd0 ?_ hord
  by_contra hlt
  push Not at hlt
  have := finite_generalLinearGroup (V := V)
  have hH0 : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have h18 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hH0).1 h2
  have hle := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).1 h2part
  have hd' : d ≤ 22 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d <;> omega

theorem three_group_of_pow_three {G : Type*} [Group G] [Finite G] (C : Subgroup G)
    (h3 : ∀ a ∈ C, a ^ 3 = 1) :
    Finite C ∧ IsPGroup 3 C ∧
      ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ P : Subgroup C, IsPGroup p P → P = ⊥ := by
  refine ⟨inferInstance, fun a => ⟨1, Subtype.ext (by simpa using h3 a a.2)⟩, ?_⟩
  intro p hp hp5 P hP
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
  have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using h3 g g.2)
  have hgk : g ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf g ∣ Nat.gcd 3 (p ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hg3) (orderOf_dvd_of_pow_eq_one hgk)
  have hcop : Nat.Coprime 3 (p ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three hp).2 (by omega))
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1 ▸ Subgroup.one_mem _

end CFSG.ComponentClassification.BMCase
