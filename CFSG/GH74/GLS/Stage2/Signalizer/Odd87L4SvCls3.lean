module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvConj
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvCls3Irred
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvCls3Cent
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvCls3Cent3
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvDefs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups commutatorElement

section Cls3

variable {F : Type} [Field F] [Finite F]

theorem l4_cls3_irred (hodd : Odd (Nat.card F)) {α : MulAut (projectiveSL 4 F)} {A : GL (Fin 4) F}
    (hA : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A) (hα : α = conjAut 4 F A * dualAut 4 F)
    (W : Submodule F (Fin 4 → F))
    (hW : ∀ A' : SL(4, F), proj 4 F A' ∈ fixSub α → ∀ w ∈ W,
      (A' : Matrix (Fin 4) (Fin 4) F) *ᵥ w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  obtain ⟨P, D, d, hd, hα₀, hD⟩ := l4_cls3_frame hodd hA
  have hα₀' : conjAut 4 F D * dualAut 4 F = conjAut 4 F P * α * (conjAut 4 F P)⁻¹ := by
    rw [hα]; exact hα₀.symm
  exact irred_transport P hα₀' (fun W₀ hW₀ => l4_cls3_irred_std hodd hd hD W₀ hW₀) W hW

theorem l4_cls3_cent (hodd : Odd (Nat.card F)) {α : MulAut (projectiveSL 4 F)} {A : GL (Fin 4) F}
    (hA : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A) (hα : α = conjAut 4 F A * dualAut 4 F)
    (x : SL(4, F))
    (h : ∀ ι : SL(2, F) →* SL(4, F), (∀ g, proj 4 F (ι g) ∈ fixSub α) →
      ∀ g, x * ι g = ι g * x) : x ∈ scalars 4 F := by
  obtain ⟨P, D, d, hd, hα₀, hD⟩ := l4_cls3_frame hodd hA
  have hα₀' : conjAut 4 F D * dualAut 4 F = conjAut 4 F P * α * (conjAut 4 F P)⁻¹ := by
    rw [hα]; exact hα₀.symm
  exact cent_transport_scalars P hα₀' (fun x₀ hx₀ => l4_cls3_cent_std hodd hd hD x₀ hx₀) x h

theorem l4_cls3_cent3 (hF : Nat.card F = 3) {α : MulAut (projectiveSL 4 F)} {A : GL (Fin 4) F}
    (hA : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A) (hα : α = conjAut 4 F A * dualAut 4 F)
    (x : SL(4, F)) (hx : ∃ r n : ℕ, r.Prime ∧ 5 ≤ r ∧ x ^ (r ^ n) = 1)
    (h : ∀ a b : SL(4, F), proj 4 F a ∈ fixSub α → proj 4 F b ∈ fixSub α →
      x * ⁅a, b⁆ = ⁅a, b⁆ * x) : x ∈ scalars 4 F := by
  obtain ⟨P, D, d, hd, hd01, hα₀, hD⟩ := l4_cls3_frame_three hF hA
  have hα₀' : conjAut 4 F D * dualAut 4 F = conjAut 4 F P * α * (conjAut 4 F P)⁻¹ := by
    rw [hα]; exact hα₀.symm
  exact cent3_transport_scalars P hα₀'
    (fun x₀ hx₀ h₀ => l4_cls3_cent3_std hF hd hd01 hD x₀ hx₀ h₀) x hx h

end Cls3

theorem l4Cls3_thm : L4Cls3 := fun _ _ _ =>
  ⟨fun hodd _ _ hA hα W hW => l4_cls3_irred hodd hA hα W hW,
   fun hodd _ _ _ hA hα x h => l4_cls3_cent hodd hA hα x h,
   fun hF _ _ hA hα x hx h => l4_cls3_cent3 hF hA hα x hx h⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
