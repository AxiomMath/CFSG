module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Eichler

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaLA

open Subgroup

@[expose] def EichU (w : V6) : Subgroup (Equiv.Perm V6) where
  carrier := {g | ∃ u : V6, bil u w = 0 ∧ ∀ x, g x = eichF w u x}
  mul_mem' := by
    rintro g h ⟨u, hu, hg⟩ ⟨u', hu', hh⟩
    refine ⟨u + u', by rw [bil_add_left, hu, hu', add_zero], fun x => ?_⟩
    rw [Equiv.Perm.mul_apply, hh, hg, eichF_comp hu hu']
  one_mem' := ⟨0, bil_zero_left w, fun x => (eichF_zero w x).symm⟩
  inv_mem' := by
    rintro g ⟨u, hu, hg⟩
    refine ⟨u, hu, fun x => ?_⟩
    rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, hg]
    exact (eichF_self hu x).symm

theorem mem_EichU {w : V6} {g : Equiv.Perm V6} :
    g ∈ EichU w ↔ ∃ u : V6, bil u w = 0 ∧ ∀ x, g x = eichF w u x := Iff.rfl

@[expose] def eichPerm (w u : V6) (hu : bil u w = 0) : Equiv.Perm V6 where
  toFun := eichF w u
  invFun := eichF w u
  left_inv := fun x => eichF_self hu x
  right_inv := fun x => eichF_self hu x

theorem eichPerm_apply {w u : V6} (hu : bil u w = 0) (x : V6) : eichPerm w u hu x = eichF w u x :=
  rfl

theorem eichPerm_mem_EichU {w u : V6} (hu : bil u w = 0) : eichPerm w u hu ∈ EichU w :=
  ⟨u, hu, fun _ => rfl⟩

private theorem zmod2_eq_one_of_ne_zero {c : ZMod 2} (h : c ≠ 0) : c = 1 := by
  have hval : c.val ≠ 0 := fun hv => h ((ZMod.val_eq_zero c).1 hv)
  have h1 : c.val = 1 := by have := ZMod.val_lt c; omega
  exact (ZMod.val_eq_one (by norm_num : 1 < 2) c).1 h1

private theorem zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  by_cases h : c = 0
  · exact Or.inl h
  · exact Or.inr (zmod2_eq_one_of_ne_zero h)

private theorem zmod2_mul_self (c : ZMod 2) : c * c = c := by
  rcases zmod2_eq_zero_or_one c with h | h <;> simp [h]

private theorem zmod2_add_self_self (p a : ZMod 2) : p + a + a = p := by
  revert p a; decide +kernel

private theorem add_self_eq_zero_V6 (x : V6) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (x i)

private theorem add_add_self_V6 (x y : V6) : x + (x + y) = y := by
  rw [← add_assoc, add_self_eq_zero_V6, zero_add]

end CFSG.EvenSporadicStandard.HNRecog.HaradaLA
