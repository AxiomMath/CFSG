module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.ComponentClassification.GHarris.K3A5

abbrev K : Type := Multiplicative (ZMod 3) × alternatingGroup (Fin 5)

@[expose] def FourPair (a b : K) : Prop :=
  a * a = 1 ∧ b * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a

instance (a b : K) : Decidable (FourPair a b) := by unfold FourPair; infer_instance

@[expose] def nCard (a b : K) : ℕ :=
  (Finset.univ.filter fun k : K => k * a * k⁻¹ ∈ ({1, a, b, a * b} : Finset K) ∧
    k * b * k⁻¹ ∈ ({1, a, b, a * b} : Finset K)).card

end CFSG.ComponentClassification.GHarris.K3A5
