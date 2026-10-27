module

public import CFSG.LieType.HighestRoot.CentChevalleySLThree
import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L4Gen

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.LieType.HighestRoot Matrix
open scoped MatrixGroups

theorem commute_of_commutator_mem {G : Type*} [Group G] {m : G} {X : Set G} {Z : Subgroup G}
    {n : ℕ} (hX : ∀ x ∈ X, x ^ n = 1) (hZ : ∀ z ∈ Z, z ^ n = 1 → z = 1)
    (hZX : ∀ z ∈ Z, ∀ x ∈ X, z * x = x * z) (h : ∀ x ∈ X, m * x * m⁻¹ * x⁻¹ ∈ Z) :
    ∀ g ∈ Subgroup.closure X, m * g = g * m :=
  CFSG.ClassicalInvolution.Q3.TA3.Q3L4.commute_of_commutator_mem hX hZ hZX h

namespace SL3

theorem sl23_mul_ne_mul :
    ∀ h s : SL23, h ^ 3 = 1 → h ≠ 1 → s ^ 4 = 1 → s ^ 2 ≠ 1 → h * s ≠ s * h := by
  decide +kernel

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2000 in
theorem sl23_exists_conj : ∀ s q : SL23, s ^ 4 = 1 → s ^ 2 ≠ 1 → q ^ 4 = 1 → q ^ 2 ≠ 1 →
    ∃ g : SL23, q * g = g * s := by
  decide +kernel

theorem sl23_exists_commutator : ∀ h : SL23, h ^ 3 = 1 → h ≠ 1 →
    ∃ g : SL23, (h * g * h⁻¹ * g⁻¹) ^ 4 = 1 ∧ h * g * h⁻¹ * g⁻¹ ≠ 1 := by
  decide +kernel

theorem sl23_pow_four : ∀ m : SL23, m ^ 4 ≠ 1 → (m ^ 4) ^ 3 = 1 := by
  decide +kernel

variable {K : Type} [Field K] [Finite K] {J : Type*} [Group J]

theorem pow_eq_one_iff_map {H : Type*} [Group H] (φ : J ≃* H) (x : J) (n : ℕ) :
    φ x ^ n = 1 ↔ x ^ n = 1 := by
  rw [← map_pow, MulEquiv.map_eq_one_iff]

theorem mul_ne_mul_of_three_four (hK : Nat.card K = 3) (e : J ≃* SL(2, K)) {h s : J}
    (h3 : h ^ 3 = 1) (h1 : h ≠ 1) (s4 : s ^ 4 = 1) (s2 : s ^ 2 ≠ 1) : h * s ≠ s * h := by
  set φ := e.trans (slEquivSL23 hK)
  intro hc
  refine sl23_mul_ne_mul (φ h) (φ s) ((pow_eq_one_iff_map φ h 3).mpr h3)
    (fun h' => h1 ((MulEquiv.map_eq_one_iff φ).mp h')) ((pow_eq_one_iff_map φ s 4).mpr s4)
    (fun h' => s2 ((pow_eq_one_iff_map φ s 2).mp h')) ?_
  rw [← map_mul, ← map_mul, hc]

theorem exists_conj_of_four (hK : Nat.card K = 3) (e : J ≃* SL(2, K)) {s q : J}
    (s4 : s ^ 4 = 1) (s2 : s ^ 2 ≠ 1) (q4 : q ^ 4 = 1) (q2 : q ^ 2 ≠ 1) :
    ∃ g : J, q * g = g * s := by
  set φ := e.trans (slEquivSL23 hK)
  obtain ⟨g, hg⟩ := sl23_exists_conj (φ s) (φ q) ((pow_eq_one_iff_map φ s 4).mpr s4)
    (fun h' => s2 ((pow_eq_one_iff_map φ s 2).mp h')) ((pow_eq_one_iff_map φ q 4).mpr q4)
    (fun h' => q2 ((pow_eq_one_iff_map φ q 2).mp h'))
  exact ⟨φ.symm g, φ.injective (by rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hg])⟩

theorem exists_commutator_of_three (hK : Nat.card K = 3) (e : J ≃* SL(2, K)) {h : J}
    (h3 : h ^ 3 = 1) (h1 : h ≠ 1) :
    ∃ g : J, (h * g * h⁻¹ * g⁻¹) ^ 4 = 1 ∧ h * g * h⁻¹ * g⁻¹ ≠ 1 := by
  set φ := e.trans (slEquivSL23 hK)
  obtain ⟨g, hg4, hg1⟩ := sl23_exists_commutator (φ h) ((pow_eq_one_iff_map φ h 3).mpr h3)
    (fun h' => h1 ((MulEquiv.map_eq_one_iff φ).mp h'))
  have hc : φ (h * φ.symm g * h⁻¹ * (φ.symm g)⁻¹) = φ h * g * (φ h)⁻¹ * g⁻¹ := by
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  refine ⟨φ.symm g, (pow_eq_one_iff_map φ _ 4).mp (by rw [hc]; exact hg4), fun h' => hg1 ?_⟩
  rw [← hc, h', map_one]

theorem pow_four_pow_three (hK : Nat.card K = 3) (e : J ≃* SL(2, K)) {m : J} (hm : m ^ 4 ≠ 1) :
    (m ^ 4) ^ 3 = 1 := by
  set φ := e.trans (slEquivSL23 hK)
  have := sl23_pow_four (φ m) (fun h' => hm ((pow_eq_one_iff_map φ m 4).mp h'))
  rwa [← map_pow, pow_eq_one_iff_map] at this

theorem le_closure_cube_of_mulEquiv (hK : Nat.card K = 3) {G : Type*} [Group G]
    {A : Subgroup G} (e : A ≃* SL(2, K)) :
    A ≤ Subgroup.closure {x : G | x ∈ A ∧ x ^ 3 = 1} := by
  intro a ha
  have hmem : (⟨a, ha⟩ : A) ∈ Subgroup.closure {x : A | orderOf x = 3} := by
    rw [closure_orderOf_three_eq_top_of_mulEquiv hK e]
    exact Subgroup.mem_top _
  have hle : Subgroup.closure {x : A | orderOf x = 3} ≤
      (Subgroup.closure {x : G | x ∈ A ∧ x ^ 3 = 1}).comap A.subtype := by
    rw [Subgroup.closure_le]
    intro x hx
    refine Subgroup.subset_closure ⟨x.2, ?_⟩
    have : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    simpa using congrArg Subtype.val this
  exact hle hmem

theorem commute_of_commutator_mem_sl23 (hK : Nat.card K = 3) {G : Type*} [Group G]
    {A Z : Subgroup G} (e : A ≃* SL(2, K)) (hZ : ∀ z ∈ Z, z ^ 3 = 1 → z = 1)
    (hZA : ∀ z ∈ Z, ∀ a ∈ A, z * a = a * z) {m : G} (h : ∀ a ∈ A, m * a * m⁻¹ * a⁻¹ ∈ Z) :
    ∀ a ∈ A, m * a = a * m := fun a ha =>
  commute_of_commutator_mem (X := {x | x ∈ A ∧ x ^ 3 = 1}) (fun _ hx => hx.2) hZ
    (fun z hz x hx => hZA z hz x hx.1) (fun x hx => h x hx.1) a
    (le_closure_cube_of_mulEquiv hK e ha)

end SL3

end CFSG.ClassicalInvolution.Q3.TA3
