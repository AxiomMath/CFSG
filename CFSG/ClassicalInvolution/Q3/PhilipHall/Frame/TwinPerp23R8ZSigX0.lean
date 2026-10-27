module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZSigE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZGen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform


@[expose] def P23E8ZSigX0 (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e →
      u * e ∈ zStarOf (rLayer (Om R) u) → SecAE R e 6 →
        ∀ x : Y, (rLayer (Om R) e).map (MulAut.conj x).toMonoidHom ≠ rLayer (Om R) e →
          rLayer (Om R) e ⊔ (rLayer (Om R) e).map (MulAut.conj x).toMonoidHom ≠ ⊤ →
            ∃ x₀ ∈ rLayer (Om R) e ⊔ (rLayer (Om R) e).map (MulAut.conj x).toMonoidHom,
              x₀ * t = t * x₀ ∧ IsPGroup 3 (Subgroup.zpowers x₀) ∧ x₀ * e * x₀⁻¹ ≠ e


variable {n : ℕ}

theorem p23E8ZSig_of_x0 (hE : TwinThmEW.ThmEQ8) (hT : Thm4RTwinBelow 3 n)
    (hα : P23Alpha n) (hN : P23E8ZNormT n) (hX : P23E8ZSigX0 n) : P23E8ZSig n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hZ hA6 x hx hne
  have hO := (p23E8Z_oddC_of_normT hE hT hα hN hcit hP hc hno hZ hA6).1
  obtain ⟨x₀, hx₀N, hx₀t, hx₀3, hx₀e⟩ := hX hcit hP Y R S t K' W u e g hc hno hZ hA6 x hx hne
  exact ZTwo.p23E8Z_sig_of_x0 hT hcit hP hc hZ hA6 hO le_sup_left hx₀N hx₀t hx₀3 hx₀e

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
