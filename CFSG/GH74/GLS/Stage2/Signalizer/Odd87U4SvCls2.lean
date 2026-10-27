module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls2Irred
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls2CentK
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls2Norm

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix Module CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped MatrixGroups commutatorElement

theorem ne_two_of_odd_pow {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hodd : Odd (p ^ f)) : p ≠ 2 := by
  rintro rfl
  have : Even (2 ^ f) := (Nat.even_pow.2 ⟨even_two, by have := h.one_le; omega⟩)
  exact (Nat.not_even_iff_odd.2 hodd) this

theorem u4_cls2_irred {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hodd : Odd (p ^ f)) (α : MulAut (hypPSU h 2 0)) (hα : SurvU4Cls2 h α)
    (W : Submodule K (HypIndex 2 0 → K))
    (hW : ∀ g : ↥(hypSU h 2 0), hypProj h 2 0 g ∈ fixSub α → ∀ w ∈ W,
      ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  obtain ⟨A, l, hx, hA, hl0, hAA, hN, rfl⟩ := hα
  obtain ⟨P, hP⟩ := exists_normal_form_u4 h (ne_two_of_odd_pow h hodd) hA hl0 hAA hN
  exact hyp_irred_transport h P hP (fun W₀ hW₀ => u4_cls2_irred_frame h hl0 hN W₀ hW₀) W hW

theorem u4_cls2_centK {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hodd : Odd (p ^ f)) (α : MulAut (hypPSU h 2 0)) (hα : SurvU4Cls2 h α)
    (x : ↥(hypSU h 2 0))
    (hx : ∀ ι : SL(2, K) →* ↥(hypSU h 2 0), (∀ g, hypProj h 2 0 (ι g) ∈ fixSub α) →
      ∀ g, x * ι g = ι g * x) :
    α (hypProj h 2 0 x) = hypProj h 2 0 x := by
  obtain ⟨A, l, hxx, hA, hl0, hAA, hN, rfl⟩ := hα
  obtain ⟨P, hP⟩ := exists_normal_form_u4 h (ne_two_of_odd_pow h hodd) hA hl0 hAA hN
  exact hyp_cent_transport_fix (H := SL(2, K)) h P hP
    (fun x₀ hx₀ => cls2_centK_frame h hl0 hN x₀ hx₀) x hx

theorem u4Cls2_thm : U4Cls2 := fun _ _ _ _ _ h =>
  ⟨fun hodd α hα W hW => u4_cls2_irred h hodd α hα W hW,
    fun hodd α hα x hx => u4_cls2_centK h hodd α hα x hx⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
