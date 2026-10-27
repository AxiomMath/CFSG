module

public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open ComplexConjugate

section Inner
variable {X : Type*} [Fintype X]

theorem cfInner_add_right (f g h : X → ℂ) :
    cfInner f (g + h) = cfInner f g + cfInner f h := by
  simp only [cfInner_def, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, mul_add]

theorem cfInner_neg_left (f h : X → ℂ) : cfInner (-f) h = -cfInner f h := by
  simp only [cfInner_def, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, mul_neg]

theorem cfInner_neg_right (f h : X → ℂ) : cfInner f (-h) = -cfInner f h := by
  simp only [cfInner_def, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib, mul_neg]

theorem cfInner_sub_left (f g h : X → ℂ) :
    cfInner (f - g) h = cfInner f h - cfInner g h := by
  simp only [cfInner_def, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]

theorem cfInner_sub_right (f g h : X → ℂ) :
    cfInner f (g - h) = cfInner f g - cfInner f h := by
  simp only [cfInner_def, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib, mul_sub]

theorem cfInner_zero_right (f : X → ℂ) : cfInner f 0 = 0 := by
  simp [cfInner_def]

theorem cfInner_self_eq_sum_normSq (f : X → ℂ) :
    cfInner f f = (Nat.card X : ℂ)⁻¹ * ((∑ x, Complex.normSq (f x) : ℝ) : ℂ) := by
  rw [cfInner_def]
  push_cast
  simp [Complex.mul_conj]

@[simp] theorem cfInner_self_eq_zero [Nonempty X] {f : X → ℂ} : cfInner f f = 0 ↔ f = 0 := by
  rw [cfInner_self_eq_sum_normSq, mul_eq_zero]
  have h : ((Nat.card X : ℂ))⁻¹ ≠ 0 := by simpa using Nat.card_pos.ne'
  simp only [h, false_or, Complex.ofReal_eq_zero]
  rw [Finset.sum_eq_zero_iff_of_nonneg fun x _ => Complex.normSq_nonneg _]
  simp [funext_iff]

end Inner

def virtualChars (G : Type*) [Group G] : Submodule ℤ (G → ℂ) := Submodule.span ℤ (Irr G)

theorem virtualChars_eq_span_Irr (G : Type*) [Group G] :
    virtualChars G = Submodule.span ℤ (Irr G) := (rfl)

theorem mem_virtualChars_iff {G : Type*} [Group G] {f : G → ℂ} :
    f ∈ virtualChars G ↔ f ∈ Submodule.span ℤ (Irr G) := Iff.rfl

theorem virtualChars_le_span_Irr {G : Type*} [Group G] :
    virtualChars G ≤ Submodule.span ℤ (Irr G) := (virtualChars_eq_span_Irr G).le

theorem mem_span_Irr_of_mem_virtualChars {G : Type*} [Group G] {f : G → ℂ}
    (hf : f ∈ virtualChars G) : f ∈ Submodule.span ℤ (Irr G) := hf

theorem mem_virtualChars_of_mem_span_Irr {G : Type*} [Group G] {f : G → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr G)) : f ∈ virtualChars G := hf

theorem coe_mem_span_Irr {G : Type*} [Group G] (f : virtualChars G) :
    (f : G → ℂ) ∈ Submodule.span ℤ (Irr G) := f.2

theorem Irr_subset_virtualChars {G : Type*} [Group G] :
    Irr G ⊆ (virtualChars G : Set (G → ℂ)) := Submodule.subset_span

theorem virtualChars_le_classFun {G : Type*} [Group G] :
    virtualChars G ≤ (classFun G).restrictScalars ℤ :=
  Submodule.span_le.2 Irr_subset_classFun

variable {L G : Type*} [Group L] [Group G]

def charSpanZero (S : Set (L → ℂ)) : Submodule ℤ (L → ℂ) :=
  Submodule.span ℤ S ⊓ LinearMap.ker (LinearMap.proj (R := ℤ) (φ := fun _ : L => ℂ) 1)

theorem mem_charSpanZero {S : Set (L → ℂ)} {f : L → ℂ} :
    f ∈ charSpanZero S ↔ f ∈ Submodule.span ℤ S ∧ f 1 = 0 := Iff.rfl

theorem charSpanZero_le (S : Set (L → ℂ)) : charSpanZero S ≤ Submodule.span ℤ S := inf_le_left

theorem charSpanZero_apply_one {S : Set (L → ℂ)} (f : charSpanZero S) : (f : L → ℂ) 1 = 0 := f.2.2

structure IsCoherentWith [Fintype L] [Fintype G] (S : Set (L → ℂ))
    (τ : charSpanZero S →+ virtualChars G) (ν : Submodule.span ℤ S →+ virtualChars G) : Prop where
  inner_eq : ∀ f h : Submodule.span ℤ S,
    cfInner (ν f : G → ℂ) (ν h : G → ℂ) = cfInner (f : L → ℂ) (h : L → ℂ)
  eq_on_zero : ∀ f : charSpanZero S, ν (Submodule.inclusion (charSpanZero_le S) f) = τ f

def IsCoherent [Fintype L] [Fintype G] (S : Set (L → ℂ))
    (τ : charSpanZero S →+ virtualChars G) : Prop :=
  ∃ ν : Submodule.span ℤ S →+ virtualChars G, IsCoherentWith S τ ν

section Coherent
variable [Fintype L] [Fintype G] {S : Set (L → ℂ)} {τ : charSpanZero S →+ virtualChars G}
  {ν : Submodule.span ℤ S →+ virtualChars G}

theorem isCoherent_iff : IsCoherent S τ ↔ ∃ ν, IsCoherentWith S τ ν := Iff.rfl

theorem IsCoherentWith.isCoherent (h : IsCoherentWith S τ ν) : IsCoherent S τ := ⟨ν, h⟩

theorem IsCoherentWith.injective (h : IsCoherentWith S τ ν) : Function.Injective ν := by
  intro f g hfg
  have key := h.inner_eq (f - g) (f - g)
  rw [map_sub, hfg, sub_self] at key
  simp only [ZeroMemClass.coe_zero, cfInner_zero_left, Submodule.coe_sub] at key
  exact Subtype.ext (sub_eq_zero.mp (cfInner_self_eq_zero.mp key.symm))

theorem IsCoherentWith.inner_eq_of_apply_one_eq_zero (h : IsCoherentWith S τ ν)
    (f g : charSpanZero S) :
    cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ) := by
  rw [← h.eq_on_zero f, ← h.eq_on_zero g]
  exact h.inner_eq _ _

theorem IsCoherent.inner_eq_of_apply_one_eq_zero (h : IsCoherent S τ) (f g : charSpanZero S) :
    cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ) := by
  obtain ⟨ν, hν⟩ := h
  exact hν.inner_eq_of_apply_one_eq_zero f g

theorem isCoherent_empty (τ : charSpanZero (∅ : Set (L → ℂ)) →+ virtualChars G) :
    IsCoherent (∅ : Set (L → ℂ)) τ := by
  have hbot : ∀ f : Submodule.span ℤ (∅ : Set (L → ℂ)), (f : L → ℂ) = 0 := by
    intro f
    have h : (f : L → ℂ) ∈ (⊥ : Submodule ℤ (L → ℂ)) := by
      rw [← Submodule.span_empty]; exact f.2
    simpa using h
  refine ⟨0, ?_, ?_⟩
  · intro f h
    simp [hbot f, hbot h, cfInner_zero_left]
  · intro f
    have hf : f = 0 := Subtype.ext (hbot ⟨(f : L → ℂ), charSpanZero_le _ f.2⟩)
    simp [hf]

end Coherent

end

end CFSG.FeitThompson
