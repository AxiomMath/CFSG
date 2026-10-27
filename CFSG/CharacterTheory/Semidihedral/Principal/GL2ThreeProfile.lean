module

public import CFSG.CharacterTheory.Semidihedral.GL2ThreeStructure

public section

namespace CFSG.Semidihedral.Principal

theorem GL2_three_neg_one_eq_Z :
    (-1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) = FourPointMatrices.Z :=
  Units.ext rfl

theorem GL2_three_element_profile_and_derived_subgroup :
    let H := Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)
    let K : Subgroup H := Matrix.GeneralLinearGroup.det.ker
    let z : H := -1
    Nat.card H = 48 ∧ orderOf z = 2 ∧ (z : Matrix (Fin 2) (Fin 2) (ZMod 3)) = -1 ∧
    Subgroup.center H = Subgroup.zpowers z ∧
    (Subgroup.center K).map K.subtype = Subgroup.zpowers z ∧
    commutator H = K ∧ K.index = 2 ∧ (∀ L : Subgroup H, L.index = 2 → L = K) ∧
    Nat.card {g : H // orderOf g = 1} = 1 ∧
    Nat.card {g : H // orderOf g = 2} = 13 ∧
    Nat.card {g : H // orderOf g = 3} = 8 ∧
    Nat.card {g : H // orderOf g = 4} = 6 ∧
    Nat.card {g : H // orderOf g = 6} = 8 ∧
    Nat.card {g : H // orderOf g = 8} = 12 ∧
    (∀ g : H, orderOf g ∈ ({1, 2, 3, 4, 6, 8} : Finset ℕ)) ∧
    (∀ a b : H, orderOf a = 3 → orderOf b = 3 → IsConj a b) ∧
    (∀ a : H, orderOf a = 3 → ∃ b : H, orderOf b = 2 ∧ b ∉ Subgroup.zpowers z ∧
      b * a * b⁻¹ = a⁻¹ ∧ Commute b z) := by
  intro H K z
  have hz : z = FourPointMatrices.Z := GL2_three_neg_one_eq_Z
  rw [hz]
  exact GL2ThreeStructure.full_structure_and_element_profile

end CFSG.Semidihedral.Principal
