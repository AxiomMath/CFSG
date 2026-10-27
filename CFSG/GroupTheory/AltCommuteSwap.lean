module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.GroupTheory

open Equiv Equiv.Perm

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

private theorem exists_alt_swap {E : Subgroup (Equiv.Perm Ω)} {a b : Equiv.Perm Ω}
    (ha : a ∈ E) (ha1 : a ≠ 1) (haa : a * a = 1) (hb : b ∈ E) (hb1 : b ≠ 1) (hba : b ≠ a)
    {x y : Ω} (hx : ∀ e ∈ E, e x = x → e = 1) (hy : ∀ e ∈ E, e y = y → e = 1)
    (hxy : ∀ e ∈ E, e x ≠ y) :
    ∃ w ∈ alternatingGroup Ω, w * a = a * w ∧ w * w = 1 ∧ w x = y ∧ w (b y) = b y := by
  classical
  have haa' : ∀ z : Ω, a (a z) = z := fun z =>
    (congrArg (fun e : Equiv.Perm Ω => e z) haa).trans (one_apply z)
  have hxy' : x ≠ y := fun h => hxy 1 (Subgroup.one_mem E) h
  have hax : a x ≠ x := fun h => ha1 (hx a ha h)
  have hay : a y ≠ y := fun h => ha1 (hy a ha h)
  have haxy : a x ≠ y := hxy a ha
  have hayx : a y ≠ x := fun h => haxy (by rw [← h, haa' y])
  obtain ⟨w, hwdef⟩ : ∃ w : Equiv.Perm Ω, w = swap x y * swap (a x) (a y) := ⟨_, rfl⟩
  have hdisj : Perm.Disjoint (swap x y) (swap (a x) (a y)) := by
    intro z
    by_cases hz : z = x ∨ z = y
    · right
      rcases hz with rfl | rfl
      · exact swap_apply_of_ne_of_ne hax.symm hayx.symm
      · exact swap_apply_of_ne_of_ne haxy.symm hay.symm
    · left
      exact swap_apply_of_ne_of_ne (fun h => hz (Or.inl h)) (fun h => hz (Or.inr h))
  have hcomm : swap x y * swap (a x) (a y) = swap (a x) (a y) * swap x y :=
    hdisj.commute
  have hwinv : w⁻¹ = w := by
    rw [hwdef, mul_inv_rev, inv_eq_of_mul_eq_one_right (swap_mul_self x y),
      inv_eq_of_mul_eq_one_right (swap_mul_self (a x) (a y))]
    exact hcomm.symm
  have hww : w * w = 1 := by
    nth_rewrite 2 [show w = w⁻¹ from hwinv.symm]
    exact mul_inv_cancel w
  have hwx : w x = y := by
    rw [hwdef]
    simp only [mul_apply]
    rw [swap_apply_of_ne_of_ne hax.symm hayx.symm, swap_apply_left]
  have hbyx : b y ≠ x := fun h => hxy b⁻¹ (E.inv_mem hb) (by
    rw [← h, ← mul_apply, inv_mul_cancel, one_apply])
  have hbyy : b y ≠ y := fun h => hb1 (hy b hb h)
  have hbyax : b y ≠ a x := fun h =>
    hxy (b⁻¹ * a) (E.mul_mem (E.inv_mem hb) ha) (by
      rw [mul_apply, ← h, ← mul_apply, inv_mul_cancel, one_apply])
  have hbyay : b y ≠ a y := by
    intro h
    have h1 : (b⁻¹ * a) y = y := by
      rw [mul_apply, ← h, ← mul_apply, inv_mul_cancel, one_apply]
    refine hba ?_
    have h2 : b⁻¹ * a = 1 := hy (b⁻¹ * a) (E.mul_mem (E.inv_mem hb) ha) h1
    calc b = b * 1 := (mul_one b).symm
      _ = b * (b⁻¹ * a) := by rw [h2]
      _ = a := by group
  have hwfix : w (b y) = b y := by
    rw [hwdef]
    simp only [mul_apply]
    rw [swap_apply_of_ne_of_ne hbyax hbyay, swap_apply_of_ne_of_ne hbyx hbyy]
  have h1 : a * swap x y * a⁻¹ = swap (a x) (a y) := (swap_apply_apply a x y).symm
  have h2 : a * swap (a x) (a y) * a⁻¹ = swap x y := by
    rw [← swap_apply_apply a (a x) (a y)]
    simp only [haa']
  have h3 : a * w * a⁻¹ = w := by
    rw [hwdef]
    have e : a * (swap x y * swap (a x) (a y)) * a⁻¹
        = (a * swap x y * a⁻¹) * (a * swap (a x) (a y) * a⁻¹) := by group
    rw [e, h1, h2, hcomm]
  have hconj : a * w = w * a := by
    calc a * w = (a * w * a⁻¹) * a := by group
      _ = w * a := by rw [h3]
  refine ⟨w, ?_, hconj.symm, hww, hwx, hwfix⟩
  rw [mem_alternatingGroup, hwdef, map_mul, sign_swap hxy', sign_swap (a.injective.ne hxy')]
  rw [neg_mul_neg, one_mul]

theorem exists_mem_alternatingGroup_commute_conj_notMem {E : Subgroup (Equiv.Perm Ω)}
    {a b : Equiv.Perm Ω} (ha : a ∈ E) (ha1 : a ≠ 1) (haa : a * a = 1) (hb : b ∈ E)
    (hb1 : b ≠ 1) (hba : b ≠ a) {x y : Ω}
    (hx : ∀ e ∈ E, e x = x → e = 1) (hy : ∀ e ∈ E, e y = y → e = 1)
    (hxy : ∀ e ∈ E, e x ≠ y) :
    ∃ w ∈ alternatingGroup Ω, w * a = a * w ∧ w * b * w⁻¹ ∉ E := by
  obtain ⟨w, hwalt, hcare, hww, hwx, hwfix⟩ :=
    exists_alt_swap ha ha1 haa hb hb1 hba hx hy hxy
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  refine ⟨w, hwalt, hcare, ?_⟩
  intro hmem
  refine hxy (b⁻¹ * (w * b * w⁻¹)) (E.mul_mem (E.inv_mem hb) hmem) ?_
  calc (b⁻¹ * (w * b * w⁻¹)) x = b⁻¹ (w (b (w⁻¹ x))) := by simp only [mul_apply]
    _ = b⁻¹ (w (b y)) := by rw [hwinv, hwx]
    _ = b⁻¹ (b y) := by rw [hwfix]
    _ = y := by rw [← mul_apply, inv_mul_cancel, one_apply]

end CFSG.GroupTheory
