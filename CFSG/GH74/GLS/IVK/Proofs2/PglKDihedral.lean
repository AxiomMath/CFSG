module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

private theorem central_map_of_equiv {P Q : Type*} [Group P] [Group Q] (θ : P ≃* Q) {z : P}
    (hzc : ∀ h : P, h * z = z * h) (h : Q) : h * θ z = θ z * h := by
  obtain ⟨h, rfl⟩ := θ.surjective h
  rw [← map_mul, ← map_mul, hzc]

private theorem centralizer_of_equiv {P Q : Type*} [Group P] [Group Q] (θ : P ≃* Q)
    (H : ∀ z a g : Q, z ≠ 1 → (∀ h : Q, h * z = z * h) → a * a = 1 → a ≠ 1 → a ≠ z →
      g * a = a * g → g = 1 ∨ g = z ∨ g = a ∨ g = a * z)
    {z a g : P} (hz1 : z ≠ 1) (hzc : ∀ h : P, h * z = z * h) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haz : a ≠ z) (hg : g * a = a * g) : g = 1 ∨ g = z ∨ g = a ∨ g = a * z := by
  rcases H (θ z) (θ a) (θ g) (θ.map_ne_one_iff.2 hz1) (central_map_of_equiv θ hzc)
      (by rw [← map_mul, ha2, map_one]) (θ.map_ne_one_iff.2 ha1) (θ.injective.ne haz)
      (by rw [← map_mul, ← map_mul, hg]) with h | h | h | h
  · exact Or.inl (θ.map_eq_one_iff.1 h)
  · exact Or.inr (Or.inl (θ.injective h))
  · exact Or.inr (Or.inr (Or.inl (θ.injective h)))
  · exact Or.inr (Or.inr (Or.inr (θ.injective (by rwa [map_mul]))))

theorem dih4_centralizer {P : Type*} [Group P] (θ : P ≃* DihedralGroup 4) {z a g : P}
    (hz1 : z ≠ 1) (hzc : ∀ h : P, h * z = z * h) (ha2 : a * a = 1) (ha1 : a ≠ 1) (haz : a ≠ z)
    (hg : g * a = a * g) : g = 1 ∨ g = z ∨ g = a ∨ g = a * z :=
  centralizer_of_equiv θ (by decide) hz1 hzc ha2 ha1 haz hg

theorem dih8_centralizer {P : Type*} [Group P] (θ : P ≃* DihedralGroup 8) {z a g : P}
    (hz1 : z ≠ 1) (hzc : ∀ h : P, h * z = z * h) (ha2 : a * a = 1) (ha1 : a ≠ 1) (haz : a ≠ z)
    (hg : g * a = a * g) : g = 1 ∨ g = z ∨ g = a ∨ g = a * z :=
  centralizer_of_equiv θ (by decide) hz1 hzc ha2 ha1 haz hg

theorem dih4_center_unique {P : Type*} [Group P] (θ : P ≃* DihedralGroup 4) {z z' : P}
    (hz1 : z ≠ 1) (hzc : ∀ h : P, h * z = z * h) (hz1' : z' ≠ 1)
    (hzc' : ∀ h : P, h * z' = z' * h) : z = z' := by
  have H : ∀ z z' : DihedralGroup 4, z ≠ 1 → (∀ h : DihedralGroup 4, h * z = z * h) → z' ≠ 1 →
      (∀ h : DihedralGroup 4, h * z' = z' * h) → z = z' := by decide
  exact θ.injective (H (θ z) (θ z') (θ.map_ne_one_iff.2 hz1) (central_map_of_equiv θ hzc)
    (θ.map_ne_one_iff.2 hz1') (central_map_of_equiv θ hzc'))

end CFSG.GH74.GLS.IVK.Proofs2
