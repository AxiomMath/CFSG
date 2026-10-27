module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.End
import Mathlib.Tactic.Abel

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {A : Type*} [AddCommGroup A]

def twoSectionStabilizer (D : AddSubgroup A) : AddSubgroup (AddAut A) where
  carrier := {t | (∀ d ∈ D, t d = d) ∧ ∀ a, t a - a ∈ D}
  zero_mem' := by simp
  add_mem' := by
    rintro t s ⟨ht₁, ht₂⟩ ⟨hs₁, hs₂⟩
    refine ⟨fun d hd => ?_, fun a => ?_⟩
    · rw [AddAut.add_apply, hs₁ d hd, ht₁ d hd]
    · rw [AddAut.add_apply]
      have h : t (s a) - a = (t (s a) - s a) + (s a - a) := by abel
      rw [h]
      exact add_mem (ht₂ _) (hs₂ a)
  neg_mem' := by
    rintro t ⟨ht₁, ht₂⟩
    refine ⟨fun d hd => ?_, fun a => ?_⟩
    · rw [AddAut.coe_neg]
      exact (AddEquiv.symm_apply_eq t).2 (ht₁ d hd).symm
    · have h : (-t) a - a = -(t ((-t) a) - (-t) a) := by
        rw [AddAut.coe_neg]
        simp
      rw [h]
      exact neg_mem (ht₂ _)

@[simp]
theorem mem_twoSectionStabilizer {D : AddSubgroup A} {t : AddAut A} :
    t ∈ twoSectionStabilizer D ↔ (∀ d ∈ D, t d = d) ∧ ∀ a, t a - a ∈ D := Iff.rfl

theorem apply_eq_self_of_mem_twoSectionStabilizer {D : AddSubgroup A} {t : AddAut A}
    (ht : t ∈ twoSectionStabilizer D) {d : A} (hd : d ∈ D) : t d = d := ht.1 d hd

theorem sub_mem_of_mem_twoSectionStabilizer {D : AddSubgroup A} {t : AddAut A}
    (ht : t ∈ twoSectionStabilizer D) (a : A) : t a - a ∈ D := ht.2 a

theorem mem_twoSectionStabilizer_of {D : AddSubgroup A} {t : AddAut A}
    (h₁ : ∀ d ∈ D, t d = d) (h₂ : ∀ a, t a - a ∈ D) : t ∈ twoSectionStabilizer D := ⟨h₁, h₂⟩

theorem apply_apply_eq_add_sub {D : AddSubgroup A} {t s : AddAut A}
    (ht : t ∈ twoSectionStabilizer D) (hs : s ∈ twoSectionStabilizer D) (a : A) :
    t (s a) = t a + (s a - a) := by
  have h : s a = a + (s a - a) := by abel
  calc t (s a) = t (a + (s a - a)) := by rw [← h]
    _ = t a + t (s a - a) := map_add _ _ _
    _ = t a + (s a - a) := by
        rw [apply_eq_self_of_mem_twoSectionStabilizer ht
          (sub_mem_of_mem_twoSectionStabilizer hs a)]

theorem apply_apply_comm_of_mem_twoSectionStabilizer {D : AddSubgroup A} {t s : AddAut A}
    (ht : t ∈ twoSectionStabilizer D) (hs : s ∈ twoSectionStabilizer D) (a : A) :
    t (s a) = s (t a) := by
  rw [apply_apply_eq_add_sub ht hs, apply_apply_eq_add_sub hs ht]
  abel

theorem add_comm_of_mem_twoSectionStabilizer {D : AddSubgroup A} {t s : AddAut A}
    (ht : t ∈ twoSectionStabilizer D) (hs : s ∈ twoSectionStabilizer D) : t + s = s + t := by
  ext a
  simpa [AddAut.add_apply] using apply_apply_comm_of_mem_twoSectionStabilizer ht hs a

instance instIsAddCommutativeTwoSectionStabilizer (D : AddSubgroup A) :
    IsAddCommutative (twoSectionStabilizer D) :=
  IsAddCommutative.of_comm fun t s =>
    Subtype.ext (add_comm_of_mem_twoSectionStabilizer t.2 s.2)

end CFSG.FeitThompson
