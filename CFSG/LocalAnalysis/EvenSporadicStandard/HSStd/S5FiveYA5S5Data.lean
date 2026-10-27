module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.EvenSporadicStandard.HSStd.FiveY

abbrev A5S5 : Type := ↥(alternatingGroup (Fin 5)) × Equiv.Perm (Fin 5)

@[expose] def cardCent (t : A5S5) : ℕ :=
  (Finset.univ.filter (fun g : A5S5 => g * t = t * g)).card

@[expose] def a5s5Stmt : Prop :=
  ∀ t : A5S5, t * t = 1 → t ≠ 1 → cardCent t = 480 →
    (∃ z : A5S5, z ≠ 1 ∧ z ≠ t ∧ z * t = t * z ∧ ∀ g : A5S5, g * t = t * g → z * g = g * z) →
    ∀ u : A5S5, u * u = 1 → u * t = t * u → (∃ w : A5S5, w * t = t * w ∧ u * w ≠ w * u) →
      ¬ ∃ c : Equiv.Perm (Fin 5), c * (t * u).2 * c⁻¹ = t.2

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
instance : Decidable a5s5Stmt := by
  unfold a5s5Stmt
  infer_instance

end CFSG.EvenSporadicStandard.HSStd.FiveY
