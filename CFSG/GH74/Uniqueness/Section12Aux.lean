module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Fixed

variable {X : Type*} [Group X]

theorem exists_commute_of_not_dvd_ncard {A : Set X} (hA : A.Finite) {x : X} {p : ℕ} (hp : p.Prime)
    (hx : orderOf x = p) (hinv : ∀ a ∈ A, x⁻¹ * a * x ∈ A) (hcard : ¬ p ∣ A.ncard) :
    ∃ a ∈ A, x * a = a * x := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite A := hA.to_subtype
  let _ : Fintype A := Fintype.ofFinite A
  have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hiter : ∀ k : ℕ, ∀ a ∈ A, (x⁻¹) ^ k * a * x ^ k ∈ A := by
    intro k
    induction k with
    | zero => intro a ha; simpa using ha
    | succ k ih =>
      intro a ha
      have := hinv _ (ih a ha)
      have e : x⁻¹ * ((x⁻¹) ^ k * a * x ^ k) * x = (x⁻¹) ^ (k + 1) * a * x ^ (k + 1) := by
        rw [pow_succ', pow_succ]; group
      rwa [e] at this
  have hback : ∀ a : X, x⁻¹ * a * x ∈ A → a ∈ A := by
    intro a ha
    have h1 := hiter (p - 1) _ ha
    have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
    have e : (x⁻¹) ^ (p - 1) * (x⁻¹ * a * x) * x ^ (p - 1) =
        (x⁻¹) ^ (p - 1 + 1) * a * x ^ (p - 1 + 1) := by
      rw [pow_succ' (x⁻¹), pow_succ x]; group
    rw [hp1] at e
    have e2 : (x⁻¹) ^ p * a * x ^ p = a := by
      rw [inv_pow, hxp, inv_one, one_mul, mul_one]
    rwa [e, e2] at h1
  let f : Equiv.Perm X :=
    { toFun := fun a => x⁻¹ * a * x
      invFun := fun a => x * a * x⁻¹
      left_inv := fun a => by group
      right_inv := fun a => by group }
  have hfa : ∀ a : X, f a = x⁻¹ * a * x := fun a => rfl
  have hf : ∀ a : X, f a ∈ A ↔ a ∈ A := by
    intro a
    rw [hfa]
    exact ⟨hback a, hinv a⟩
  have hpow : ∀ k : ℕ, ∀ a : X, (f ^ k) a = (x⁻¹) ^ k * a * x ^ k := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      rw [pow_succ, Equiv.Perm.mul_apply, hfa, ih, pow_succ (x⁻¹) k, pow_succ' x k]
      group
  have h1 : f ^ p = 1 := by
    ext a
    rw [hpow, inv_pow, hxp, inv_one, one_mul, mul_one]
    rfl
  have hσ : (f.subtypePerm hf) ^ p ^ 1 = 1 := by
    rw [pow_one, Equiv.Perm.subtypePerm_pow]
    ext a
    simp [h1]
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (n := 1) (by
    rwa [Fintype.card_eq_nat_card, Nat.card_coe_set_eq]) hσ
  refine ⟨a, a.2, ?_⟩
  have h2 : f a = a := congrArg Subtype.val ha
  have h3 : x⁻¹ * (a : X) * x = a := by rw [← hfa]; exact h2
  calc x * (a : X) = x * (x⁻¹ * a * x) := by rw [h3]
    _ = a * x := by group

end Fixed

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_mem_of_card_eq {p : ℕ} [Fact p.Prime] {R : Subgroup G}
    (hR : Nat.card R = p ^ (Nat.card G).factorization p) {x : G} (hx : IsPGroup p (zpowers x)) :
    ∃ g : G, g * x * g⁻¹ ∈ R := by
  let P : Sylow p G := Sylow.ofCard R hR
  obtain ⟨Q, hQ⟩ := hx.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨g, ?_⟩
  have hxQ : x ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers x)
  have : g * x * g⁻¹ ∈ ((g • Q : Sylow p G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨x, hxQ, by simp [MulAut.smul_def]⟩
  rw [hg] at this
  exact this

end Sylow

end CFSG.GH74.Uniqueness
