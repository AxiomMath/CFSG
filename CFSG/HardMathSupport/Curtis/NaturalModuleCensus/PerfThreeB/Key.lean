module

public import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Tactic.Abel
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeB

variable {V : Type*} [AddCommGroup V]

structure IsoData (B : V → V → ZMod 2) (f : V → V) : Prop where
  two : ∀ x : V, x + x = 0
  Badd_l : ∀ x y z, B (x + y) z = B x z + B y z
  Badd_r : ∀ x y z, B x (y + z) = B x y + B x z
  fadd : ∀ x y, f (x + y) = f x + f y
  alt : ∀ x, B x x = 0
  symm : ∀ x y, B x y = B y x
  nondeg : ∀ x, x ≠ 0 → ∃ y, B x y = 1
  pow3 : ∀ x, f (f (f x)) = x
  isom : ∀ x y, B (f x) (f y) = B x y

theorem zmod_two_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

variable {B : V → V → ZMod 2} {f : V → V}

theorem IsoData.neg_eq (h : IsoData B f) (x : V) : -x = x := by
  rw [neg_eq_iff_add_eq_zero]
  exact h.two x

theorem IsoData.isom2 (h : IsoData B f) (x y : V) : B (f (f x)) (f (f y)) = B x y := by
  rw [h.isom, h.isom]

theorem IsoData.f_zero (h : IsoData B f) : f 0 = 0 := by
  have := h.fadd 0 0
  rw [add_zero] at this
  exact (left_eq_add.mp this)

theorem IsoData.injective (h : IsoData B f) {x : V} (hx : f x = 0) : x = 0 := by
  rw [← h.pow3 x, hx, h.f_zero, h.f_zero]

theorem IsoData.case_fixed (h : IsoData B f) {a : V} (ha0 : a ≠ 0) (hfa : f a = a) :
    ∃ c, f c = c ∧ B a c = 1 := by
  obtain ⟨c', hc'⟩ := h.nondeg a ha0
  refine ⟨c' + f c' + f (f c'), ?_, ?_⟩
  · rw [h.fadd, h.fadd, h.pow3]
    abel
  · have e1 : B a (f c') = B a c' := by
      have := h.isom a c'
      rwa [hfa] at this
    have e2 : B a (f (f c')) = B a c' := by
      have := h.isom2 a c'
      rwa [hfa, hfa] at this
    rw [h.Badd_r, h.Badd_r, e1, e2, hc']
    decide

theorem IsoData.exists_dual (h : IsoData B f) {a : V} (hfa0 : f a ≠ 0)
    (hfane : f a ≠ a) : ∃ d, B a d = 0 ∧ B (f a) d = 1 := by
  obtain ⟨db, hdb⟩ := h.nondeg (f a) hfa0
  have hsum : a + f a ≠ 0 := by
    intro h0
    apply hfane
    have := eq_neg_of_add_eq_zero_right h0
    rw [h.neg_eq] at this
    exact this
  obtain ⟨d1, hd1⟩ := h.nondeg (a + f a) hsum
  rw [h.Badd_l] at hd1
  rcases zmod_two_cases (B a db) with h0 | h0
  · exact ⟨db, h0, hdb⟩
  · rcases zmod_two_cases (B a d1) with h1 | h1
    · refine ⟨d1, h1, ?_⟩
      rw [h1, zero_add] at hd1
      exact hd1
    · refine ⟨d1 + db, ?_, ?_⟩
      · rw [h.Badd_r, h0, h1]; decide
      · rw [h.Badd_r, hdb]
        rw [h1] at hd1
        have : B (f a) d1 = 0 := by
          have h2 : (1 : ZMod 2) + B (f a) d1 = 1 := hd1
          have := congrArg (· - 1) h2
          simpa using this
        rw [this]; decide

theorem IsoData.exists_good (h : IsoData B f) {a : V} (hBafa : B a (f a) = 0)
    (hf2 : f (f a) = a + f a) {d : V} (hd0 : B a d = 0) (hd1 : B (f a) d = 1) :
    ∃ b, B a b = 0 ∧ B (f a) b = 1 ∧ B b (f b) = 0 := by
  rcases zmod_two_cases (B d (f d)) with hq | hq
  · exact ⟨d, hd0, hd1, hq⟩
  · refine ⟨d + f a, ?_, ?_, ?_⟩
    · rw [h.Badd_r, hd0, hBafa]; decide
    · rw [h.Badd_r, hd1, h.alt]; decide
    · have e1 : B (f a) (f d) = 0 := by rw [h.isom]; exact hd0
      have e2 : B (f a) (f (f a)) = 0 := by rw [h.isom]; exact hBafa
      have e3 : B d (f (f a)) = 1 := by
        rw [hf2, h.Badd_r, h.symm d a, hd0, h.symm d (f a), hd1]; decide
      rw [h.fadd, h.Badd_l, h.Badd_r, h.Badd_r, hq, e1, e2, e3]
      decide

theorem IsoData.case_free (h : IsoData B f) (F : AddSubgroup V)
    (hiso : ∀ x ∈ F, ∀ y ∈ F, B x y = 0) (hf : ∀ x ∈ F, f x ∈ F) {a : V} (haF : a ∈ F)
    (ha0 : a ≠ 0) (hfix : ∀ x ∈ F, x ≠ 0 → f x ≠ x) :
    ∃ b, B b (f b) = 0 ∧ B a b = 0 ∧ B a (f b) = 1 ∧ B a (f (f b)) = 1 ∧
      B (f b + f (f b)) (f a) = 1 := by
  have hfaF : f a ∈ F := hf a haF
  have hfa0 : f a ≠ 0 := fun h0 => ha0 (h.injective h0)
  have hfane : f a ≠ a := hfix a haF ha0
  have hBafa : B a (f a) = 0 := hiso a haF (f a) hfaF
  have hf2 : f (f a) = a + f a := by
    have hw : a + f a + f (f a) = 0 := by
      by_contra hne
      have hwF : a + f a + f (f a) ∈ F := F.add_mem (F.add_mem haF hfaF) (hf _ hfaF)
      apply hfix _ hwF hne
      rw [h.fadd, h.fadd, h.pow3]
      abel
    have := eq_neg_of_add_eq_zero_right hw
    rw [h.neg_eq] at this
    exact this
  obtain ⟨d, hd0, hd1⟩ := h.exists_dual hfa0 hfane
  obtain ⟨b, hb0, hb1, hbq⟩ := h.exists_good hBafa hf2 hd0 hd1
  have e1 : B a (f b) = 1 := by
    have := h.isom2 a (f b)
    rw [h.pow3, hf2, h.Badd_l, hb0, hb1] at this
    rw [← this]; decide
  have e2 : B a (f (f b)) = 1 := by
    have := h.isom a (f (f b))
    rw [h.pow3] at this
    rw [← this, hb1]
  refine ⟨b, hbq, hb0, e1, e2, ?_⟩
  have e3 : B (f b) (f a) = 0 := by
    rw [h.isom, h.symm, hb0]
  have e4 : B (f (f b)) (f a) = 1 := by
    rw [h.isom, h.symm, e1]
  rw [h.Badd_l, e3, e4]; decide

theorem IsoData.key (h : IsoData B f) (F : AddSubgroup V)
    (hiso : ∀ x ∈ F, ∀ y ∈ F, B x y = 0) (hf : ∀ x ∈ F, f x ∈ F) {a0 : V} (ha0F : a0 ∈ F)
    (ha0 : a0 ≠ 0) :
    (∃ a ∈ F, ∃ c, f c = c ∧ B a c = 1) ∨
      (∃ a ∈ F, ∃ b, B b (f b) = 0 ∧ B a b = 0 ∧ B a (f b) = 1 ∧ B a (f (f b)) = 1 ∧
        B (f b + f (f b)) (f a) = 1) := by
  by_cases hfix : ∃ a ∈ F, a ≠ 0 ∧ f a = a
  · obtain ⟨a, haF, ha0, hfa⟩ := hfix
    obtain ⟨c, hc⟩ := h.case_fixed ha0 hfa
    exact Or.inl ⟨a, haF, c, hc⟩
  · push Not at hfix
    exact Or.inr ⟨a0, ha0F, h.case_free F hiso hf ha0F ha0 hfix⟩

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeB
