module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls1Frame
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls1Cent

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix Module CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped MatrixGroups commutatorElement

section Cls1

variable {p f : ℕ} {K : Type} [Field K]

theorem u4_ne_two_of_odd_pow (h : UnitaryFieldData p f K) (hodd : Odd (p ^ f)) : p ≠ 2 := by
  rintro rfl
  have h1 := h.one_le
  exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow' (by omega)).2 even_two)

theorem u4_cls1_conj (h : UnitaryFieldData p f K) (hodd : Odd (p ^ f))
    {α : MulAut (hypPSU h 2 0)} (hα : SurvU4Cls1 h α) :
    ∃ Q : ↥(hypUnitary h 2 0),
      U4C1.u4Alpha0 h = hypPhi h Q * α * (hypPhi h Q)⁻¹ := by
  obtain ⟨A, l, hx, hA, hl0, hAA, hN, hdim, rfl⟩ := hα
  obtain ⟨P, hP⟩ := U4C1.u4_exists_P h (u4_ne_two_of_odd_pow h hodd) hA hl0 hAA hN hdim
  exact ⟨P⁻¹, U4C1.u4_alpha0_eq h (A := ⟨A, hA⟩) hl0 hN hP⟩

theorem u4_cls1_irred (h : UnitaryFieldData p f K) (hodd : Odd (p ^ f))
    {α : MulAut (hypPSU h 2 0)} (hα : SurvU4Cls1 h α) (W : Submodule K (HypIndex 2 0 → K))
    (hW : ∀ g : ↥(hypSU h 2 0), hypProj h 2 0 g ∈ fixSub α → ∀ w ∈ W,
      ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  obtain ⟨Q, hQ⟩ := u4_cls1_conj h hodd hα
  exact hyp_irred_transport h Q hQ (fun W₀ hW₀ => U4C1.u4_cls1_irred_std h W₀ hW₀) W hW

theorem u4_cls1_cent (h : UnitaryFieldData p f K) (hodd : Odd (p ^ f))
    {α : MulAut (hypPSU h 2 0)} (hα : SurvU4Cls1 h α) (x : ↥(hypSU h 2 0))
    (hx : ∀ ι : SL(2, ↥h.fixedField) →* ↥(hypSU h 2 0),
      (∀ g, hypProj h 2 0 (ι g) ∈ fixSub α) → ∀ g, x * ι g = ι g * x) :
    α (hypProj h 2 0 x) = hypProj h 2 0 x := by
  obtain ⟨Q, hQ⟩ := u4_cls1_conj h hodd hα
  exact hyp_cent_transport_fix (H := SL(2, ↥h.fixedField)) h Q hQ
    (fun x₀ hx₀ => U4C1.u4_cls1_cent_std h x₀ hx₀) x hx

theorem u4_cls1_cent3 (h : UnitaryFieldData p f K) (hq3 : p ^ f = 3)
    {α : MulAut (hypPSU h 2 0)} (hα : SurvU4Cls1 h α) (x : ↥(hypSU h 2 0))
    (hr : ∃ r n : ℕ, r.Prime ∧ 5 ≤ r ∧ x ^ (r ^ n) = 1)
    (hc : ∀ a b : ↥(hypSU h 2 0), hypProj h 2 0 a ∈ fixSub α → hypProj h 2 0 b ∈ fixSub α →
      x * ⁅a, b⁆ = ⁅a, b⁆ * x) :
    α (hypProj h 2 0 x) = hypProj h 2 0 x := by
  obtain ⟨Q, hQ⟩ := u4_cls1_conj h (by rw [hq3]; exact ⟨1, rfl⟩) hα
  exact hyp_cent3_transport_fix h Q hQ (fun x₀ _ hc₀ => U4C1.u4_cls1_cent3_std h hq3 x₀ hc₀) x hr hc

end Cls1

theorem u4Cls1_thm : U4Cls1 := fun _ _ _ _ _ h =>
  ⟨fun hodd _ hα W hW => u4_cls1_irred h hodd hα W hW,
    fun hodd _ _ hα x hx => u4_cls1_cent h hodd hα x hx,
    fun hq3 _ hα x hr hc => u4_cls1_cent3 h hq3 hα x hr hc⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
