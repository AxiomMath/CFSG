module

public import CFSG.GH74.QTGen4.U42.U0AutC

public section

namespace CFSG.GH74.QTGen4.U42

open U0AutC

theorem three_part_sup_eq (P P' S : Subgroup (MulAut U0))
    (hP : Nat.card P = 9) (hP' : Nat.card P' = 9) (hI : Inn0 ≤ S) :
    P ⊔ S = P' ⊔ S := by
  calc
    P ⊔ S = (P ⊔ Inn0) ⊔ S := by rw [sup_assoc, sup_eq_right.mpr hI]
    _ = (P' ⊔ Inn0) ⊔ S := by rw [three_part_unique P P' hP hP']
    _ = P' ⊔ S := by rw [sup_assoc, sup_eq_right.mpr hI]

theorem three_part_normal (P : Subgroup (MulAut U0)) (hP : Nat.card P = 9) :
    (P ⊔ Inn0).Normal := by
  constructor
  intro x hx a
  let c : MulAut (MulAut U0) := MulAut.conj a
  have hc : Nat.card (P.map c.toMonoidHom) = 9 :=
    (Subgroup.card_map_of_injective c.injective).trans hP
  have hI : Inn0.map c.toMonoidHom ≤ Inn0 := by
    rintro y ⟨z, hz, rfl⟩
    exact Inn0_normal.conj_mem z hz a
  have hm : (P ⊔ Inn0).map c.toMonoidHom ≤ P.map c.toMonoidHom ⊔ Inn0 := by
    rw [Subgroup.map_sup]
    exact sup_le le_sup_left (hI.trans le_sup_right)
  have hcx : c x ∈ P.map c.toMonoidHom ⊔ Inn0 := hm ⟨x, hx, rfl⟩
  rw [three_part_unique (P.map c.toMonoidHom) P hc hP] at hcx
  exact hcx

theorem three_part_comap_normal {K : Type*} [Group K]
    (f : K →* MulAut U0) (P : Subgroup (MulAut U0)) (hP : Nat.card P = 9) :
    ((P ⊔ Inn0).comap f).Normal := by
  letI : (P ⊔ Inn0).Normal := three_part_normal P hP
  infer_instance

theorem three_part_comap_cube {K : Type*} [Group K]
    (f : K →* MulAut U0) (P : Subgroup (MulAut U0)) (hP : Nat.card P = 9) :
    ∀ x ∈ (P ⊔ Inn0).comap f, x ^ 3 ∈ Inn0.comap f := by
  intro x hx
  change f (x ^ 3) ∈ Inn0
  rw [map_pow]
  exact three_part_cube P hP (f x) hx

end CFSG.GH74.QTGen4.U42
