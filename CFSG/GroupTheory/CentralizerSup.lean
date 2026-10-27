module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

public section

namespace CFSG

theorem centralizer_sup_eq {G : Type*} [Group G] (H K : Subgroup G) :
    Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) =
      Subgroup.centralizer (H : Set G) ⊓ Subgroup.centralizer (K : Set G) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨fun y hy => h y (Subgroup.mem_sup_left hy),
      fun y hy => h y (Subgroup.mem_sup_right hy)⟩
  · rintro ⟨hH, hK⟩ y hy
    have hle : H ⊔ K ≤ Subgroup.centralizer ({x} : Set G) :=
      sup_le (fun y hy => (Subgroup.mem_centralizer_singleton_iff).2 (hH y hy))
        (fun y hy => (Subgroup.mem_centralizer_singleton_iff).2 (hK y hy))
    exact (Subgroup.mem_centralizer_singleton_iff).1 (hle hy)

theorem centralizer_zpowers_eq_centralizer_singleton {G : Type*} [Group G] (b : G) :
    Subgroup.centralizer (Subgroup.zpowers b : Set G) = Subgroup.centralizer ({b} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem centralizer_sup_zpowers_eq {G : Type*} [Group G] (H : Subgroup G) (b : G) :
    Subgroup.centralizer ((H ⊔ Subgroup.zpowers b : Subgroup G) : Set G) =
      Subgroup.centralizer (H : Set G) ⊓ Subgroup.centralizer ({b} : Set G) := by
  rw [centralizer_sup_eq, centralizer_zpowers_eq_centralizer_singleton]

end CFSG

end
