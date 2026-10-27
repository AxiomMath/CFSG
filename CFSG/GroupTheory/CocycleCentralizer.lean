module

public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG.GroupTheory

theorem mem_centralizer_of_cocycle_eq_one
    {A G : Type*} [Group A] [Group G] (i : A →* G) (c : A → G)
    (hcomm : ∀ a b : A, a * b = b * a)
    (hc : ∀ a b, c (a * b) = c a * (i a * c b * (i a)⁻¹))
    (F : Subgroup A) (hF : ∀ a ∈ F, c a = 1) (a : A) :
    c a ∈ Subgroup.centralizer (Set.range (fun b : F => i b.val)) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨b, rfl⟩
  have h₁ := hc a b.val
  have h₂ := hc b.val a
  rw [hF b.val b.property, mul_one, mul_inv_cancel, mul_one] at h₁
  rw [hF b.val b.property, one_mul] at h₂
  have hh : c a = i b.val * c a * (i b.val)⁻¹ := by
    rw [hcomm a b.val] at h₁
    exact h₁.symm.trans h₂
  exact (eq_mul_inv_iff_mul_eq.mp hh).symm

theorem exists_monoidHom_of_cocycle_centralizer_eq
    {A G : Type*} [Group A] [Group G] (i : A →* G) (c : A → G)
    (hcomm : ∀ a b : A, a * b = b * a)
    (hc : ∀ a b, c (a * b) = c a * (i a * c b * (i a)⁻¹))
    (F : Subgroup A) (hF : ∀ a ∈ F, c a = 1)
    (hdet : Subgroup.centralizer (Set.range (fun b : F => i b.val)) =
      Subgroup.centralizer (Set.range i)) :
    ∃ f : A →* G, (∀ a, f a = c a) ∧
      f.range ≤ Subgroup.centralizer (Set.range i) := by
  have hcent (a) : c a ∈ Subgroup.centralizer (Set.range i) :=
    hdet ▸ mem_centralizer_of_cocycle_eq_one i c hcomm hc F hF a
  have hmul (a b) : c (a * b) = c a * c b := by
    have hh := (Subgroup.mem_centralizer_iff.mp (hcent b)) (i a) (Set.mem_range_self a)
    rw [hc a b, hh, mul_assoc, mul_inv_cancel, mul_one]
  let f : A →* G :=
    { toFun := c
      map_one' := by
        have hh := hmul 1 1
        rw [one_mul] at hh
        exact mul_left_cancel (hh.symm.trans (mul_one (c 1)).symm)
      map_mul' := hmul }
  refine ⟨f, fun _ => rfl, ?_⟩
  rintro _ ⟨a, rfl⟩
  exact hcent a


end CFSG.GroupTheory
