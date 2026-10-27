module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls3Std
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls3Frame
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvDefs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix Module CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped MatrixGroups

section Odd

variable {p f : ℕ} {K : Type} [Field K]

theorem u4c3_ne_two_of_odd_pow (h : UnitaryFieldData p f K) (hodd : Odd (p ^ f)) : p ≠ 2 := by
  rintro rfl
  have := h.one_le
  have h2 : Even (2 ^ f) := (Nat.even_pow' (by omega)).mpr even_two
  exact (Nat.not_even_iff_odd.mpr hodd) h2

end Odd

section Main

variable {p f : ℕ} {K : Type} [Field K] [Finite K]

theorem u4_cls3_irred (h : UnitaryFieldData p f K) (hodd : Odd (p ^ f))
    (α : MulAut (hypPSU h 2 0)) (hα : SurvU4Cls3 h α) (W : Submodule K (HypIndex 2 0 → K))
    (hW : ∀ g : ↥(hypSU h 2 0), hypProj h 2 0 g ∈ fixSub α → ∀ w ∈ W,
      ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  obtain ⟨A, σ, hx, hA, hσ, hAA, hα'⟩ := hα
  have hp := u4c3_ne_two_of_odd_pow h hodd
  obtain ⟨E, d, hd, hgram, hfix⟩ := u4_cls3_frame h hp hA hAA
  exact u4_cls3_irred_frame ⟨hd, hgram, hfix⟩ hA hAA hp hα' hσ W hW

theorem u4_cls3_cent (h : UnitaryFieldData p f K) (hodd : Odd (p ^ f))
    (α : MulAut (hypPSU h 2 0)) (hα : SurvU4Cls3 h α) (x : ↥(hypSU h 2 0))
    (hxc : ∀ ι : SL(2, ↥h.fixedField) →* ↥(hypSU h 2 0), (∀ g, hypProj h 2 0 (ι g) ∈ fixSub α) →
      ∀ g, x * ι g = ι g * x) : x ∈ hypScalars h 2 0 := by
  obtain ⟨A, σ, hx, hA, hσ, hAA, hα'⟩ := hα
  have hp := u4c3_ne_two_of_odd_pow h hodd
  obtain ⟨E, d, hd, hgram, hfix⟩ := u4_cls3_frame h hp hA hAA
  exact u4_cls3_cent_frame ⟨hd, hgram, hfix⟩ hA hAA hp hα' hσ x hxc

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
