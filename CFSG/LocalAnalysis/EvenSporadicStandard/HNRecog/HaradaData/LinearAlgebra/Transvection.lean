module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.LinearAlgebra.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaLA

abbrev IsQF (q : V6 → ZMod 2) : Prop := ∀ x y, q (x + y) = q x + q y + bil x y

theorem transv_apply (u x : V6) : transv u x = x + bil x u • u := rfl

private theorem zmod2_eq_one_of_ne_zero {c : ZMod 2} (h : c ≠ 0) : c = 1 := by
  have hval : c.val ≠ 0 := fun hv => h ((ZMod.val_eq_zero c).1 hv)
  have h1 : c.val = 1 := by have := ZMod.val_lt c; omega
  exact (ZMod.val_eq_one (by norm_num : 1 < 2) c).1 h1

private theorem zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  by_cases h : c = 0
  · exact Or.inl h
  · exact Or.inr (zmod2_eq_one_of_ne_zero h)

private theorem add_self_eq_zero_V6 (x : V6) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (x i)

private theorem perm_zero {g : Equiv.Perm V6} (hg : IsAddPerm g) : g 0 = 0 := by
  have h : g 0 = g 0 + g 0 := by simpa using hg 0 0
  rwa [add_self_eq_zero_V6] at h

private theorem perm_smul {g : Equiv.Perm V6} (hg : IsAddPerm g) (c : ZMod 2) (v : V6) :
    g (c • v) = c • g v := by
  by_cases hc : c = 0
  · rw [hc, zero_smul, zero_smul]; exact perm_zero hg
  · rw [zmod2_eq_one_of_ne_zero hc, one_smul, one_smul]

private theorem bil_eq {q : V6 → ZMod 2} (hq : IsQF q) (a b : V6) :
    bil a b = q (a + b) + q a + q b := by
  have h := hq a b
  rw [h]
  rw [show (q a + q b + bil a b) + q a + q b
        = bil a b + (q a + q b + (q a + q b)) by abel]
  rw [CharTwo.add_self_eq_zero, add_zero]

theorem transv_mul_self (u : V6) : transv u * transv u = 1 := by
  apply Equiv.Perm.ext
  intro x
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, transv_apply]
  exact transv_involutive x u

theorem isAddPerm_transv (u : V6) : IsAddPerm (transv u) := by
  intro x y
  simp only [transv_apply, bil_add_left, add_smul]
  abel

theorem transv_apply_of_bil_eq_zero {u x : V6} (h : bil x u = 0) : transv u x = x := by
  rw [transv_apply, h, zero_smul, add_zero]

theorem transv_mem_orthOf {q : V6 → ZMod 2} (hq : IsQF q) {u : V6} (hu : q u = 1) :
    transv u ∈ OrthOf q := by
  refine ⟨isAddPerm_transv u, fun x => ?_⟩
  rw [transv_apply]
  by_cases hc : bil x u = 0
  · rw [hc, zero_smul, add_zero]
  · rw [zmod2_eq_one_of_ne_zero hc, one_smul, hq x u, hu, zmod2_eq_one_of_ne_zero hc]
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem bil_apply_of_mem_orthOf {q : V6 → ZMod 2} (hq : IsQF q) {g : Equiv.Perm V6}
    (hg : g ∈ OrthOf q) (x y : V6) : bil (g x) (g y) = bil x y := by
  obtain ⟨hgadd, hgq⟩ := hg
  rw [bil_eq hq (g x) (g y), ← hgadd x y, hgq (x + y), hgq x, hgq y]
  exact (bil_eq hq x y).symm

theorem conj_transv {q : V6 → ZMod 2} (hq : IsQF q) {g : Equiv.Perm V6} (hg : g ∈ OrthOf q)
    (u : V6) : g * transv u * g⁻¹ = transv (g u) := by
  ext x
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_def,
    transv_apply, transv_apply, hg.1, perm_smul hg.1,
    ← bil_apply_of_mem_orthOf hq hg (g.symm x) u, Equiv.apply_symm_apply]

end CFSG.EvenSporadicStandard.HNRecog.HaradaLA
