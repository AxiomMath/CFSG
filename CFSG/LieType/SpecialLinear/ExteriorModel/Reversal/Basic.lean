module

public import CFSG.LieType.SpecialLinear.ExteriorModel.Minor

public section

open Module

namespace CFSG.LieType.SpecialLinear.ExteriorModel

open Matrix

variable {R : Type*} [CommRing R] {m n : ℕ}

@[expose] noncomputable def complEquiv (h : n ≤ m) :
    Set.powersetCard (Fin m) n ≃ Set.powersetCard (Fin m) (m - n) :=
  Set.powersetCard.compl (α := Fin m) (n := n) (m := m - n)
    (by simpa using Nat.sub_add_cancel h)

@[simp]
theorem coe_complEquiv (h : n ≤ m) (s : Set.powersetCard (Fin m) n) :
    ((complEquiv h s : Set.powersetCard (Fin m) (m - n)) : Finset (Fin m)) =
      (s : Finset (Fin m))ᶜ :=
  rfl

@[simp]
theorem mem_complEquiv (h : n ≤ m) (s : Set.powersetCard (Fin m) n) (a : Fin m) :
    a ∈ (complEquiv h s : Set.powersetCard (Fin m) (m - n)) ↔ a ∉ (s : Finset (Fin m)) := by
  rw [complEquiv, Set.powersetCard.mem_compl]
  exact not_congr Set.powersetCard.mem_coe_iff

@[expose] noncomputable def permImage (π : Equiv.Perm (Fin m))
    (s : Set.powersetCard (Fin m) n) : Set.powersetCard (Fin m) n :=
  ⟨s.val.image π, by
    rw [Set.powersetCard.mem_iff, Finset.card_image_of_injective _ π.injective, s.prop]⟩

@[simp]
theorem coe_permImage (π : Equiv.Perm (Fin m)) (s : Set.powersetCard (Fin m) n) :
    ((permImage π s : Set.powersetCard (Fin m) n) : Finset (Fin m)) =
      (s : Finset (Fin m)).image π :=
  rfl

@[simp]
theorem mem_permImage (π : Equiv.Perm (Fin m)) (s : Set.powersetCard (Fin m) n) (a : Fin m) :
    a ∈ (permImage π s : Set.powersetCard (Fin m) n) ↔
      π.symm a ∈ (s : Finset (Fin m)) := by
  change a ∈ (s.val.image π) ↔ π.symm a ∈ s.val
  rw [Finset.mem_image]
  constructor
  · rintro ⟨b, hb, rfl⟩
    simpa using hb
  · intro ha
    exact ⟨π.symm a, ha, by simp⟩

@[simp]
theorem mem_permImage_coe (π : Equiv.Perm (Fin m)) (s : Set.powersetCard (Fin m) n)
    (a : Fin m) :
    a ∈ ((permImage π s : Set.powersetCard (Fin m) n) : Finset (Fin m)) ↔
      π.symm a ∈ (s : Finset (Fin m)) :=
  mem_permImage π s a

@[simp]
theorem permImage_permImage (π σ : Equiv.Perm (Fin m))
    (s : Set.powersetCard (Fin m) n) :
    permImage π (permImage σ s) = permImage (π * σ) s := by
  apply Subtype.ext
  simp [permImage, Finset.image_image, Function.comp_def]

@[simp]
theorem permImage_one (s : Set.powersetCard (Fin m) n) :
    permImage (1 : Equiv.Perm (Fin m)) s = s := by
  apply Subtype.ext
  simp [permImage]

@[simp]
theorem permImage_revPerm_mul_self (s : Set.powersetCard (Fin m) n) :
    permImage ((Fin.revPerm : Equiv.Perm (Fin m)) * Fin.revPerm) s = s := by
  rw [show (Fin.revPerm : Equiv.Perm (Fin m)) * Fin.revPerm = 1 by
    ext i
    simp, permImage_one]

@[expose] noncomputable def revEquiv :
    Set.powersetCard (Fin m) n ≃ Set.powersetCard (Fin m) n where
  toFun := permImage (Fin.revPerm : Equiv.Perm (Fin m))
  invFun := permImage (Fin.revPerm : Equiv.Perm (Fin m))
  left_inv s := by
    have h : (Fin.revPerm : Equiv.Perm (Fin m)) * Fin.revPerm = 1 := by
      ext i
      simp
    rw [permImage_permImage, h]
    ext a
    simp [permImage]
  right_inv s := by
    have h : (Fin.revPerm : Equiv.Perm (Fin m)) * Fin.revPerm = 1 := by
      ext i
      simp
    rw [permImage_permImage, h]
    ext a
    simp [permImage]

@[simp]
theorem revEquiv_apply (s : Set.powersetCard (Fin m) n) :
    revEquiv s = permImage (Fin.revPerm : Equiv.Perm (Fin m)) s :=
  rfl

@[simp]
theorem revEquiv_symm : (revEquiv (m := m) (n := n)).symm = revEquiv (m := m) (n := n) := by
  ext s
  rfl

@[simp]
theorem revEquiv_revEquiv (s : Set.powersetCard (Fin m) n) :
    revEquiv (revEquiv s) = s := by
  rw [← revEquiv_symm]
  exact Equiv.symm_apply_apply revEquiv s

@[simp]
theorem mem_revEquiv (s : Set.powersetCard (Fin m) n) (a : Fin m) :
    a ∈ (revEquiv s : Set.powersetCard (Fin m) n) ↔
      Fin.rev a ∈ (s : Finset (Fin m)) := by
  rw [revEquiv_apply, mem_permImage]
  simp [Fin.revPerm_symm]

@[simp]
theorem mem_revEquiv_coe (s : Set.powersetCard (Fin m) n) (a : Fin m) :
    a ∈ ((revEquiv s : Set.powersetCard (Fin m) n) : Finset (Fin m)) ↔
      Fin.rev a ∈ (s : Finset (Fin m)) :=
  mem_revEquiv s a

@[simp]
theorem mem_complEquiv_coe (h : n ≤ m) (s : Set.powersetCard (Fin m) n) (a : Fin m) :
    a ∈ ((complEquiv h s : Set.powersetCard (Fin m) (m - n)) : Finset (Fin m)) ↔
      a ∉ (s : Finset (Fin m)) :=
  mem_complEquiv h s a

end CFSG.LieType.SpecialLinear.ExteriorModel
