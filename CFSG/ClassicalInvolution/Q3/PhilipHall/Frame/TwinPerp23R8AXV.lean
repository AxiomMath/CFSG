module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AE

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section AXV

@[expose] def P23E8ACaseB (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → SecAE R u 5 → SecAE R e 6 →
      alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥ →
      ∀ y ∈ rLayer (Om R) u, y * t = t * y → IsPGroup 3 (Subgroup.zpowers y) →
        (∀ o ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)), y * e * y⁻¹ ≠ o * e * o⁻¹) →
          ¬ ∀ x ∈ rLayer (Om R) (t * e), (t * (y * e * y⁻¹)) * x = x * (t * (y * e * y⁻¹))

@[expose] def P23E8AXV (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → SecAE R u 5 → SecAE R e 6 →
      alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥ →
        ∃ (b : Y) (V : Subgroup Y), V ≤ p23XE R e b ∧
          (∀ x ∈ p23XE R e b, ∀ v ∈ V, x * v * x⁻¹ ∈ V) ∧ IsPGroup 2 V ∧
          t ∈ V ∧ e ∈ V ∧ b * e * b⁻¹ ∈ V ∧
          conjSub b (rLayer (Om R) e) ≠ rLayer (Om R) e ∧
          ∃ J ∈ Om R, J ≤ rLayer (Om R) e ∧ J ≤ conjSub b (rLayer (Om R) e)

end AXV

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
