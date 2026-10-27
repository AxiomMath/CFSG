module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.ComponentClassification.HSFLit

open Subgroup DihedralGroup

theorem exists_prodDihedral_equiv {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hAB : A ⊓ B = ⊥) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hcard : Nat.card A * Nat.card B = Nat.card G) (eA : A ≃* DihedralGroup 4)
    (eB : B ≃* DihedralGroup 4) :
    ∃ φ : G ≃* DihedralGroup 4 × DihedralGroup 4,
      (∀ a : A, φ a = (eA a, 1)) ∧ (∀ b : B, φ b = (1, eB b)) := by
  set f : DihedralGroup 4 × DihedralGroup 4 →* G :=
    (A.subtype.comp eA.symm.toMonoidHom).noncommCoprod (B.subtype.comp eB.symm.toMonoidHom)
      (fun p q => hcomm _ (eA.symm p).2 _ (eB.symm q).2) with hf
  have hfapp : ∀ p q, f (p, q) = (eA.symm p : G) * (eB.symm q : G) := fun _ _ => rfl
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨p, q⟩ hpq
    rw [MonoidHom.mem_ker, hfapp] at hpq
    have hmem : (eA.symm p : G) ∈ A ⊓ B := by
      refine Subgroup.mem_inf.mpr ⟨(eA.symm p).2, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hpq]
      exact inv_mem (eB.symm q).2
    rw [hAB, mem_bot] at hmem
    have hp : p = 1 := by
      have : eA.symm p = 1 := Subtype.ext hmem
      simpa using congrArg eA this
    rw [hmem, one_mul] at hpq
    have hq : q = 1 := by
      have : eB.symm q = 1 := Subtype.ext hpq
      simpa using congrArg eB this
    rw [hp, hq]
    exact one_mem _
  have hbij : Function.Bijective f := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [← hcard, Nat.card_prod, Nat.card_congr eA.toEquiv, Nat.card_congr eB.toEquiv]
  set e := MulEquiv.ofBijective f hbij
  refine ⟨e.symm, fun a => ?_, fun b => ?_⟩
  · rw [MulEquiv.symm_apply_eq]
    change (a : G) = f (eA a, 1)
    rw [hfapp]
    simp
  · rw [MulEquiv.symm_apply_eq]
    change (b : G) = f (1, eB b)
    rw [hfapp]
    simp

theorem eq_r_two_of_central (d : DihedralGroup 4) (hd : ∀ h, d * h = h * d) (hd2 : d ^ 2 = 1)
    (hd1 : d ≠ 1) : d = r 2 := by
  revert d
  decide

theorem eq_r_two_or_exists_commutator (d : DihedralGroup 4) (hd1 : d ≠ 1) :
    d = r 2 ∨ ∃ h, d * h * d⁻¹ * h⁻¹ = r 2 := by
  revert d
  decide

theorem eq_of_commute_noncentral (d p : DihedralGroup 4) (hd2 : d ^ 2 = 1) (hd1 : d ≠ 1)
    (hdr : d ≠ r 2) (hp : p * d = d * p) : p = 1 ∨ p = r 2 ∨ p = d ∨ p = r 2 * d := by
  revert d p
  decide

theorem dd_eq_of_commutator (g : DihedralGroup 4 × DihedralGroup 4)
    (hg : ∀ h : DihedralGroup 4 × DihedralGroup 4,
      g * h * g⁻¹ * h⁻¹ = 1 ∨ g * h * g⁻¹ * h⁻¹ = (r 2, r 2)) :
    g = 1 ∨ g = (r 2, 1) ∨ g = (1, r 2) ∨ g = (r 2, r 2) := by
  revert g
  decide

theorem dd_eq_of_central (g : DihedralGroup 4 × DihedralGroup 4)
    (hg : ∀ h : DihedralGroup 4 × DihedralGroup 4, g * h = h * g) :
    g = 1 ∨ g = (r 2, 1) ∨ g = (1, r 2) ∨ g = (r 2, r 2) :=
  dd_eq_of_commutator g fun h => Or.inl (by rw [hg h, mul_inv_cancel_right, mul_inv_cancel])

theorem dd_r_two_r_two_central (q : DihedralGroup 4 × DihedralGroup 4) :
    (r 2, r 2) * q = q * (r 2, r 2) := by
  revert q
  decide

theorem dd_card_sq_eq_left :
    Nat.card {g : DihedralGroup 4 × DihedralGroup 4 // g ^ 2 = (r 2, 1)} = 12 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem dd_card_sq_eq_right :
    Nat.card {g : DihedralGroup 4 × DihedralGroup 4 // g ^ 2 = (1, r 2)} = 12 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem dd_card_sq_eq_both :
    Nat.card {g : DihedralGroup 4 × DihedralGroup 4 // g ^ 2 = (r 2, r 2)} = 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

end CFSG.ComponentClassification.HSFLit
