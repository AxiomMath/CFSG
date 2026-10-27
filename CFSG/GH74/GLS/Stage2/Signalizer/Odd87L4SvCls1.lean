module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvCls1Irred
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvCls1Cent
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvConj
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvDefs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Orth3Mod

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups commutatorElement

section Cls1

variable {F : Type} [Field F] [Finite F]

theorem l4_cls1_conj (hodd : Odd (Nat.card F)) {α : MulAut (projectiveSL 4 F)} {B : GL (Fin 4) F}
    (hB : B * B = 1) (hr : Module.finrank F (LinearMap.ker (toLin' B.val - 1)) = 2)
    (hα : α = conjAut 4 F B) :
    ∃ P : GL (Fin 4) F,
      conjAut 4 F (B0 F) = conjAut 4 F P * α * (conjAut 4 F P)⁻¹ := by
  obtain ⟨P, hP⟩ := exists_frame_cls1 (two_ne_zero_of_odd_card hodd) hB hr
  refine ⟨P⁻¹, ?_⟩
  rw [hα, hP]
  simp only [map_mul, map_inv]
  group

theorem l4_cls1_irred (hodd : Odd (Nat.card F)) {α : MulAut (projectiveSL 4 F)} {B : GL (Fin 4) F}
    (hB : B * B = 1) (hr : Module.finrank F (LinearMap.ker (toLin' B.val - 1)) = 2)
    (hα : α = conjAut 4 F B) (W : Submodule F (Fin 4 → F))
    (hW : ∀ A : SL(4, F), proj 4 F A ∈ fixSub α → ∀ w ∈ W,
      (A : Matrix (Fin 4) (Fin 4) F) *ᵥ w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  obtain ⟨P, hP⟩ := l4_cls1_conj hodd hB hr hα
  exact irred_transport P hP (fun W₀ hW₀ => l4_cls1_irred_std W₀ hW₀) W hW

theorem l4_cls1_cent (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) {α : MulAut (projectiveSL 4 F)}
    {B : GL (Fin 4) F} (hB : B * B = 1)
    (hr : Module.finrank F (LinearMap.ker (toLin' B.val - 1)) = 2) (hα : α = conjAut 4 F B)
    (x : SL(4, F))
    (h : ∀ ι : SL(2, F) →* SL(4, F), (∀ g, proj 4 F (ι g) ∈ fixSub α) → ∀ g, x * ι g = ι g * x) :
    α (proj 4 F x) = proj 4 F x := by
  have _ := h5
  obtain ⟨P, hP⟩ := l4_cls1_conj hodd hB hr hα
  exact cent_transport_fix P hP (fun x₀ hx₀ => l4_cls1_cent_std x₀ hx₀) x h

theorem l4_cls1_cent3 (hF : Nat.card F = 3) {α : MulAut (projectiveSL 4 F)} {B : GL (Fin 4) F}
    (hB : B * B = 1) (hr : Module.finrank F (LinearMap.ker (toLin' B.val - 1)) = 2)
    (hα : α = conjAut 4 F B) (x : SL(4, F)) (hx : ∃ r n : ℕ, r.Prime ∧ 5 ≤ r ∧ x ^ (r ^ n) = 1)
    (h : ∀ a b : SL(4, F), proj 4 F a ∈ fixSub α → proj 4 F b ∈ fixSub α →
      x * ⁅a, b⁆ = ⁅a, b⁆ * x) :
    α (proj 4 F x) = proj 4 F x := by
  have hodd : Odd (Nat.card F) := by rw [hF]; decide
  obtain ⟨P, hP⟩ := l4_cls1_conj hodd hB hr hα
  exact cent3_transport_fix P hP (fun x₀ _ hx₀ => l4_cls1_cent3_std hF x₀ hx₀) x hx h

theorem l4Cls1_thm : L4Cls1 := fun _ _ _ =>
  ⟨fun hodd {_α} {_B} hB hr hα W hW => l4_cls1_irred hodd hB hr hα W hW,
    fun hodd h5 {_α} {_B} hB hr hα x h => l4_cls1_cent hodd h5 hB hr hα x h,
    fun hF {_α} {_B} hB hr hα x hx h => l4_cls1_cent3 hF hB hr hα x hx h⟩

end Cls1

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
