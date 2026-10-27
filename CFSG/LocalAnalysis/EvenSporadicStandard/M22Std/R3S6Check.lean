module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.EvenSporadicStandard.M22Std.S6Check

@[expose] def cS6 (u : Equiv.Perm (Fin 6)) : ℕ :=
  Fintype.card {c : Equiv.Perm (Fin 6) // c * u = u * c}

@[expose] def cA6 (u : Equiv.Perm (Fin 6)) : ℕ :=
  Fintype.card {c : alternatingGroup (Fin 6) // (c : Equiv.Perm (Fin 6)) * u = u * c}

@[expose] def S6Prop1 : Prop :=
  ∀ u : Equiv.Perm (Fin 6), u * u = 1 →
    16 ∣ cS6 u ∧ ∃ c : Equiv.Perm (Fin 6), c * u = u * c ∧ Equiv.Perm.sign c = -1

instance : Decidable S6Prop1 := by
  unfold S6Prop1 cS6
  infer_instance

@[expose] def invData : Finset (ℕ × Bool) :=
  (Finset.univ.filter fun u : Equiv.Perm (Fin 6) => u * u = 1).image
    fun u => (cA6 u, decide (u ≠ 1))

@[expose] def S6Prop2 : Prop :=
  ∀ x ∈ invData, ∀ y ∈ invData, (x.2 = true ∨ y.2 = true) → ¬ (x.1 * y.1 ∣ 1440)

instance : Decidable S6Prop2 := by
  unfold S6Prop2
  infer_instance

theorem S6Prop2.apply (h : S6Prop2) {u v : Equiv.Perm (Fin 6)} (hu : u * u = 1) (hv : v * v = 1)
    (huv : u ≠ 1 ∨ v ≠ 1) : ¬ (cA6 u * cA6 v ∣ 1440) := by
  refine h (cA6 u, decide (u ≠ 1)) ?_ (cA6 v, decide (v ≠ 1)) ?_ ?_
  · exact Finset.mem_image.2 ⟨u, Finset.mem_filter.2 ⟨Finset.mem_univ _, hu⟩, rfl⟩
  · exact Finset.mem_image.2 ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ _, hv⟩, rfl⟩
  · simpa only [decide_eq_true_eq] using huv

@[expose] def S6Prop : Prop := S6Prop1 ∧ S6Prop2

instance : Decidable S6Prop := by
  unfold S6Prop
  infer_instance

@[expose] def s6Check : Bool := decide S6Prop

end CFSG.EvenSporadicStandard.M22Std.S6Check
