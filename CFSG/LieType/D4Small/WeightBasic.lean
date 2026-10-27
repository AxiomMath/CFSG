module

public import CFSG.LieType.D4Small.Weights

public section

namespace CFSG.LieType.D4Small.D4Datum

attribute [local instance] Fintype.ofFinite Classical.propDecidable

theorem add_self_eq_zero (K : Type*) [Field K] [CharP K 2] {X : Type*} [AddCommGroup X]
    [Module K X] (x : X) : x + x = 0 := by
  rw [← two_smul K x, CharTwo.two_eq_zero, zero_smul]

variable {G : Type*} [Group G] {K : Type*} [Field K] [Finite K] [CharP K 2]
  (D : D4Datum G K) {X : Type*} [AddCommGroup X] [Module K X] (ρ : Representation K G X)

theorem forall_mem_of_rootElt {M : Submodule K X}
    (hM : ∀ α, IsD4Root α → ∀ c : K, ∀ x ∈ M, ρ (D.x α c) x ∈ M) :
    ∀ g : G, ∀ x ∈ M, ρ g x ∈ M := by
  intro g
  have hg : g ∈ Subgroup.closure {g | ∃ α, IsD4Root α ∧ ∃ c, D.x α c = g} := by
    rw [D.closure_eq]
    exact Subgroup.mem_top g
  suffices h : (∀ x ∈ M, ρ g x ∈ M) ∧ ∀ x ∈ M, ρ g⁻¹ x ∈ M from h.1
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨α, hα, c, rfl⟩ := hg
    refine ⟨hM α hα c, ?_⟩
    rw [← D.x_neg hα]
    exact hM α hα (-c)
  | one => exact ⟨fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩
  | mul g h _ _ ihg ihh =>
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [map_mul, Module.End.mul_apply]
      exact ihg.1 _ (ihh.1 x hx)
    · rw [mul_inv_rev, map_mul, Module.End.mul_apply]
      exact ihh.2 _ (ihg.2 x hx)
  | inv g _ ihg => exact ⟨ihg.2, by simpa using ihg.1⟩

theorem eq_zero_of_mem_wtSpace_of_mem_wtSpace {a b : Fin 4 → ZMod (Nat.card Kˣ)} (hab : a ≠ b)
    {x : X} (ha : x ∈ D.wtSpace ρ a) (hb : x ∈ D.wtSpace ρ b) : x = 0 := by
  have h1 := wtProj_of_mem D ρ (a := a) ha
  have h2 := wtProj_of_mem D ρ (a := a) hb
  rw [if_pos rfl] at h1
  rw [if_neg hab] at h2
  rw [← h1, h2]

theorem eq_zero_of_add_mem {a b : Fin 4 → ZMod (Nat.card Kˣ)} (hab : a ≠ b) {x y : X}
    (hx : x ∈ D.wtSpace ρ a) (hy : y ∈ D.wtSpace ρ b) (hxy : x + y ∈ D.wtSpace ρ b) : x = 0 := by
  have hxb : x ∈ D.wtSpace ρ b := by
    have h := Submodule.sub_mem _ hxy hy
    rwa [add_sub_cancel_right] at h
  exact eq_zero_of_mem_wtSpace_of_mem_wtSpace D ρ hab hx hxb

variable {D ρ} {C : Finset (Fin 4 → ZMod (Nat.card Kˣ))}

theorem eq_zero_of_mem_wtSpace_of_not_mem (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∉ C) {x : X} (hx : x ∈ D.wtSpace ρ a) : x = 0 := by
  have hbot : D.wtSpace ρ a = ⊥ := by
    by_contra h
    exact ha ((hCw a).mpr h)
  rw [hbot] at hx
  exact (Submodule.mem_bot K).mp hx

theorem rootOp_apply_eq_zero (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥) {α : Fin 4 → ℤ}
    (hα : IsD4Root α) {a : Fin 4 → ZMod (Nat.card Kˣ)} {x : X} (hx : x ∈ D.wtSpace ρ a) {k : ℕ}
    (hk : a + (k : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) α ∉ C) : rootOp D ρ α k x = 0 :=
  eq_zero_of_mem_wtSpace_of_not_mem hCw hk (rootOp_mem_wtSpace D ρ α hα a hx k)

theorem ext_of_wtSpace (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥) {f g : Module.End K X}
    (h : ∀ a ∈ C, ∀ x ∈ D.wtSpace ρ a, f x = g x) : f = g := by
  ext x
  rw [← sum_wtProj D ρ x, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : a ∈ C
  · exact h a ha _ (wtProj_mem D ρ a x)
  · rw [eq_zero_of_mem_wtSpace_of_not_mem hCw ha (wtProj_mem D ρ a x), map_zero, map_zero]

end CFSG.LieType.D4Small.D4Datum
