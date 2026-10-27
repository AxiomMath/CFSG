module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem exists_fixed_mul_of_not_dvd {F : Type*} [FunLike F G G] [MonoidHomClass F G G] (α : F)
    (hα : ∀ g, α (α (α g)) = g) (N : Subgroup G) [Finite N] (hN3 : ¬3 ∣ Nat.card N)
    (hN : ∀ m ∈ N, α m ∈ N) {w : G} (hw : w⁻¹ * α w ∈ N) : ∃ m ∈ N, α (w * m) = w * m := by
  classical
  have : Fintype N := Fintype.ofFinite N
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmem : ∀ m : N, w⁻¹ * α (w * m) ∈ N := fun m => by
    rw [map_mul, ← mul_assoc]
    exact N.mul_mem hw (hN _ m.2)
  set f : N → N := fun m => ⟨w⁻¹ * α (w * m), hmem m⟩ with hf
  have hf3 : ∀ m, f (f (f m)) = m := by
    intro m
    apply Subtype.ext
    simp only [hf, mul_inv_cancel_left, hα, inv_mul_cancel_left]
  let σ : Equiv.Perm N := ⟨f, fun m => f (f m), fun m => hf3 m, fun m => hf3 m⟩
  have hσ : σ ^ 3 ^ 1 = 1 := by
    refine Equiv.ext fun m => ?_
    simp only [pow_one, pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact hf3 m
  obtain ⟨m, hm⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1)
    (by rwa [← Nat.card_eq_fintype_card]) hσ
  refine ⟨m, m.2, ?_⟩
  have h : w⁻¹ * α (w * m) = m := congrArg Subtype.val hm
  calc α (w * m) = w * (w⁻¹ * α (w * m)) := by group
    _ = w * m := by rw [h]

theorem pow_eq_one_of_mem_closure {S : Set G} (hS : S.Pairwise Commute) {n : ℕ}
    (hn : ∀ s ∈ S, s ^ n = 1) {g : G} (hg : g ∈ Subgroup.closure S) : g ^ n = 1 := by
  have hle := Subgroup.closure_le_centralizer_centralizer S
  have hc : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, Commute x y := fun x hx y hy =>
    Set.centralizer_centralizer_comm_of_comm hS x (hle hx) y (hle hy)
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hn x hx
  | one => exact one_pow n
  | mul x y hx hy ihx ihy => rw [(hc x hx y hy).mul_pow, ihx, ihy, one_mul]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

theorem not_dvd_card_of_pow_eq_one {p n : ℕ} (hp : p.Prime) (hpn : ¬p ∣ n) (H : Subgroup G)
    [Finite H] (hH : ∀ g ∈ H, g ^ n = 1) : ¬p ∣ Nat.card H := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have h1 : x ^ n = 1 := Subtype.ext (by simpa using hH x x.2)
  exact hpn (hx ▸ orderOf_dvd_of_pow_eq_one h1)

@[expose] def commModSubgroup (N : Subgroup G) (x : G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (N : Set G) ∧ x * g * x⁻¹ * g⁻¹ ∈ N}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(Subgroup.normalizer (N : Set G)).mul_mem ha hb, ?_⟩
    have e : x * (a * b) * x⁻¹ * (a * b)⁻¹ =
        (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e]
    exact N.mul_mem ha' ((Subgroup.mem_normalizer_iff.1 ha _).1 hb')
  one_mem' := ⟨(Subgroup.normalizer (N : Set G)).one_mem, by simpa using N.one_mem⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(Subgroup.normalizer (N : Set G)).inv_mem ha, ?_⟩
    have e : x * a⁻¹ * x⁻¹ * a⁻¹⁻¹ = a⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (N : Set G)).inv_mem ha) _).1
      (N.inv_mem ha')

theorem commutatorElement_mul_of_commute {x v n : G} (h : Commute x n) : ⁅x, v * n⁆ = ⁅x, v⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have h' : n * x⁻¹ = x⁻¹ * n := h.inv_left.eq.symm
  calc x * (v * n) * x⁻¹ * (v * n)⁻¹ = x * v * (n * x⁻¹) * n⁻¹ * v⁻¹ := by group
    _ = x * v * x⁻¹ * v⁻¹ := by rw [h']; group

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen
