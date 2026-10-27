module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.CGT.Foote82

namespace CaseIS6D8

open DihedralGroup

variable {Γ : Type*} [Group Γ]

@[expose] def dihHom (u w : Γ) (hu : u ^ 4 = 1) (hw : w * w = 1) (hwu : w * u * w⁻¹ = u⁻¹) :
    DihedralGroup 4 →* Γ where
  toFun x := match x with
    | DihedralGroup.r i => u ^ i.val
    | DihedralGroup.sr i => w * u ^ i.val
  map_one' := by
    show u ^ (0 : ZMod 4).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' := by
    have hA : ∀ a b : ZMod 4, u ^ a.val * u ^ b.val = u ^ (a + b).val := fun a b => by
      rw [← pow_add, pow_eq_pow_mod (a.val + b.val) hu, ← ZMod.val_add]
    have hB : ∀ i j : ZMod 4, u ^ (j - i).val = (u ^ i.val)⁻¹ * u ^ j.val := fun i j => by
      apply eq_inv_mul_of_mul_eq
      rw [hA, add_sub_cancel]
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
    have hC : ∀ k : ℕ, u ^ k * w = w * (u ^ k)⁻¹ := fun k => by
      have h1 : w * u ^ k * w⁻¹ = (u ^ k)⁻¹ := by rw [← conj_pow, hwu, inv_pow]
      calc u ^ k * w = w * (w⁻¹ * u ^ k * w) := by group
        _ = w * (w * u ^ k * w⁻¹) := by rw [hwinv]
        _ = w * (u ^ k)⁻¹ := by rw [h1]
    rintro (i | i) (j | j)
    · show u ^ (i + j).val = u ^ i.val * u ^ j.val
      rw [hA]
    · show w * u ^ (j - i).val = u ^ i.val * (w * u ^ j.val)
      rw [← mul_assoc, hC, hB, mul_assoc]
    · show w * u ^ (i + j).val = w * u ^ i.val * u ^ j.val
      rw [mul_assoc, hA]
    · show u ^ (j - i).val = w * u ^ i.val * (w * u ^ j.val)
      rw [hB, mul_assoc w, ← mul_assoc (u ^ i.val), hC, ← mul_assoc, ← mul_assoc, hw, one_mul]

variable {u w : Γ} {hu : u ^ 4 = 1} {hw : w * w = 1} {hwu : w * u * w⁻¹ = u⁻¹}

theorem dihHom_r (i : ZMod 4) : dihHom u w hu hw hwu (r i) = u ^ i.val := rfl

theorem dihHom_sr (i : ZMod 4) : dihHom u w hu hw hwu (sr i) = w * u ^ i.val := rfl

theorem dihHom_mem {K : Subgroup Γ} (huK : u ∈ K) (hwK : w ∈ K) (x : DihedralGroup 4) :
    dihHom u w hu hw hwu x ∈ K := by
  rcases x with i | i
  · exact K.pow_mem huK _
  · exact K.mul_mem hwK (K.pow_mem huK _)

theorem dihHom_commute {g : Γ} (hgu : Commute u g) (hgw : Commute w g) (x : DihedralGroup 4) :
    Commute (dihHom u w hu hw hwu x) g := by
  rcases x with i | i
  · exact hgu.pow_left _
  · exact hgw.mul_left (hgu.pow_left _)

theorem dihHom_injective (hu4 : orderOf u = 4) (hwu' : ∀ k : ℕ, w ≠ u ^ k) :
    Function.Injective (dihHom u w hu hw hwu) := by
  rw [injective_iff_map_eq_one]
  rintro (i | i) h
  · rw [dihHom_r] at h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hu4] at h1
    have h2 : i.val < 4 := ZMod.val_lt i
    have h3 : i.val = 0 := by
      rcases h1 with ⟨c, hc⟩
      rcases c with _ | c
      · simpa using hc
      · omega
    rw [show i = 0 from (ZMod.val_eq_zero i).1 h3]
    rfl
  · rw [dihHom_sr] at h
    exfalso
    apply hwu' (4 - i.val)
    have h1 : w = (u ^ i.val)⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [h1]
    have h2 : i.val ≤ 4 := (ZMod.val_lt i).le
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_add, Nat.sub_add_cancel h2, hu]

theorem r_two_mem_center : (r 2 : DihedralGroup 4) ∈ Subgroup.center (DihedralGroup 4) := by
  rw [DihedralGroup.center_eq_closure_of_even_ne_two (by decide) (by decide)]
  exact Subgroup.mem_zpowers _

theorem card_center : Nat.card (Subgroup.center (DihedralGroup 4)) = 2 := by
  rw [DihedralGroup.center_eq_closure_of_even_ne_two (by decide) (by decide), Nat.card_zpowers,
    DihedralGroup.orderOf_r]
  rfl

theorem card_center_prod :
    Nat.card (Subgroup.center (DihedralGroup 4 × DihedralGroup 4)) = 4 := by
  rw [Subgroup.center_prod, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    card_center]

theorem card_prod : Nat.card (DihedralGroup 4 × DihedralGroup 4) = 64 := by
  rw [Nat.card_prod, DihedralGroup.nat_card]

end CaseIS6D8

end CFSG.CGT.Foote82
