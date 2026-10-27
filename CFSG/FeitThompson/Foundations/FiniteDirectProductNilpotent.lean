module

public import Mathlib.GroupTheory.Nilpotent

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped commutatorElement

theorem commutator_eq_closure_conjugates {G : Type*} [Group G] (A B : Subgroup G) :
    ⁅A, B⁆ = Subgroup.closure {g | ∃ a ∈ A, ∃ b ∈ B, a⁻¹ * b⁻¹ * a * b = g} := by
  rw [Subgroup.commutator_def]
  congr 1
  ext g
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, by group⟩

theorem isNilpotent_iff_exists_normal_central_series (X : Type*) [Group X] :
    Group.IsNilpotent X ↔ ∃ (r : ℕ) (S : ℕ → Subgroup X), S 0 = ⊥ ∧ S r = ⊤ ∧
      (∀ i, S i ≤ S (i + 1)) ∧ (∀ i, (S i).Normal) ∧
      ∀ i, ⁅(⊤ : Subgroup X), S (i + 1)⁆ ≤ S i := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := (Group.isNilpotent_iff X).1 h
    refine ⟨r, Subgroup.upperCentralSeries X, Subgroup.upperCentralSeries_zero X, hr,
      fun i => Subgroup.upperCentralSeries_mono X (Nat.le_succ i), fun i => inferInstance,
      fun i => ?_⟩
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_upperCentralSeries_top_le X i
  · rintro ⟨r, S, h0, hr, -, -, hcomm⟩
    rw [Subgroup.nilpotent_iff_finite_ascending_central_series]
    refine ⟨r, S, ⟨h0, fun x n hx g => ?_⟩, hr⟩
    have h1 : ⁅g, x⁆ ∈ S n :=
      hcomm n (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) hx)
    simpa using inv_mem h1

theorem subsingleton_pi_fin_zero (G : Fin 0 → Type*) [∀ i, Group (G i)] :
    Subsingleton (∀ i, G i) :=
  ⟨fun _ _ => funext fun i => i.elim0⟩

theorem exists_normal_central_series_pi {n : ℕ} (G : Fin n → Type*) [∀ i, Group (G i)]
    (h : ∀ i, ∃ (r : ℕ) (S : ℕ → Subgroup (G i)), S 0 = ⊥ ∧ S r = ⊤ ∧
      (∀ j, S j ≤ S (j + 1)) ∧ (∀ j, (S j).Normal) ∧
      ∀ j, ⁅(⊤ : Subgroup (G i)), S (j + 1)⁆ ≤ S j) :
    ∃ (r : ℕ) (S : ℕ → Subgroup (∀ i, G i)), S 0 = ⊥ ∧ S r = ⊤ ∧
      (∀ j, S j ≤ S (j + 1)) ∧ (∀ j, (S j).Normal) ∧
      ∀ j, ⁅(⊤ : Subgroup (∀ i, G i)), S (j + 1)⁆ ≤ S j := by
  have : ∀ i, Group.IsNilpotent (G i) := fun i =>
    (isNilpotent_iff_exists_normal_central_series (G i)).2 (h i)
  exact (isNilpotent_iff_exists_normal_central_series _).1 Group.isNilpotent_pi

end CFSG.FeitThompson
