module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup

variable {G : Type} [Group G]

theorem t6_inv_of_fpf {A : Subgroup G} [Finite A] {g : G} (hg : g * g = 1)
    (hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ A) (hfix : ∀ a ∈ A, g * a * g⁻¹ = a → a = 1) :
    (∀ a ∈ A, g * a * g⁻¹ = a⁻¹) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  let f : A → A := fun a => ⟨(a : G)⁻¹ * (g * a * g⁻¹), A.mul_mem (A.inv_mem a.2) (hgA a a.2)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : (a : G)⁻¹ * (g * a * g⁻¹) = (b : G)⁻¹ * (g * b * g⁻¹) := congrArg Subtype.val hab
    have h2 : g * ((b : G) * (a : G)⁻¹) * g⁻¹ = (b : G) * (a : G)⁻¹ := by
      have : g * ((b : G) * (a : G)⁻¹) * g⁻¹ = (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹ := by group
      rw [this]
      have h3 : g * b * g⁻¹ = (b : G) * ((a : G)⁻¹ * (g * a * g⁻¹)) := by
        rw [h1]; group
      rw [h3]
      group
    have h4 := hfix _ (A.mul_mem b.2 (A.inv_mem a.2)) h2
    have : (b : G) = a := by
      calc (b : G) = ((b : G) * (a : G)⁻¹) * a := by group
        _ = a := by rw [h4]; simp
    exact Subtype.ext this.symm
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.1 hf
  have hinv : ∀ a ∈ A, g * a * g⁻¹ = a⁻¹ := by
    intro c hc
    obtain ⟨a, ha⟩ := hsurj ⟨c, hc⟩
    have hca : c = (a : G)⁻¹ * (g * a * g⁻¹) := congrArg Subtype.val ha.symm
    rw [hca]
    have e : g * ((a : G)⁻¹ * (g * a * g⁻¹)) * g⁻¹ = g * (a : G)⁻¹ * g * a * (g⁻¹ * g⁻¹) := by group
    have e2 : g⁻¹ * g⁻¹ = 1 := by rw [hginv, hg]
    rw [e, e2, mul_one]
    simp only [mul_inv_rev, inv_inv, hginv, mul_assoc]
  refine ⟨hinv, fun a ha b hb => ?_⟩
  have h1 := hinv (a * b) (A.mul_mem ha hb)
  have h2 : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
  rw [h2, hinv a ha, hinv b hb] at h1
  have h3 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by
    rw [h1]; group
  calc a * b = (b⁻¹ * a⁻¹)⁻¹ := by group
    _ = (a⁻¹ * b⁻¹)⁻¹ := by rw [h3]
    _ = b * a := by group

theorem t6_odd_of_pGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G} (hP : IsPGroup p P) {x : G}
    (hx : x ∈ P) : Odd (orderOf x) := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hk' : x ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hdvd : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  exact hodd.of_dvd_nat hdvd

omit [Group G] in
theorem t6_norm_sup {G : Type} [Group G] {A B : Subgroup G} {g : G} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ B) : ∀ x ∈ A ⊔ B, g * x * g⁻¹ ∈ A ⊔ B := by
  intro x hx
  rw [Subgroup.sup_eq_closure] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact Subgroup.subset_closure (Or.inl (hA y hy))
    · exact Subgroup.subset_closure (Or.inr (hB y hy))
  | one => simp
  | mul a b _ _ ha hb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]; exact Subgroup.inv_mem _ ha

omit [Group G] in
theorem t6_comm_sup {G : Type} [Group G] {A B : Subgroup G} {x : G} (hA : ∀ a ∈ A, x * a = a * x)
    (hB : ∀ b ∈ B, x * b = b * x) : ∀ y ∈ A ⊔ B, x * y = y * x := by
  intro y hy
  rw [Subgroup.sup_eq_closure] at hy
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact hA y hy
    · exact hB y hy
  | one => simp
  | mul a b _ _ ha hb =>
    calc x * (a * b) = (x * a) * b := by group
      _ = (a * x) * b := by rw [ha]
      _ = a * (x * b) := by group
      _ = a * (b * x) := by rw [hb]
      _ = (a * b) * x := by group
  | inv a _ ha =>
    calc x * a⁻¹ = a⁻¹ * (a * x) * a⁻¹ := by group
      _ = a⁻¹ * (x * a) * a⁻¹ := by rw [ha]
      _ = a⁻¹ * x := by group

end CFSG.GH74.GLS.Stage4.Rest.T6
