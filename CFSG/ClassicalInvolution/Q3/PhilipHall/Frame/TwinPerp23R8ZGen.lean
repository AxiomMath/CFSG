module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R56Sigma

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section E8ZGen

@[expose] def P23E8ZGen (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e →
      u * e ∈ zStarOf (rLayer (Om R) u) → SecAE R e 6 →
        ∀ x : Y, (rLayer (Om R) e).map (MulAut.conj x).toMonoidHom ≠ rLayer (Om R) e →
          rLayer (Om R) e ⊔ (rLayer (Om R) e).map (MulAut.conj x).toMonoidHom = ⊤

@[expose] def P23E8ZLay (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e →
      u * e ∈ zStarOf (rLayer (Om R) u) → SecAE R e 6 →
        ∀ J ∈ tqMembers3 (Om R) u, J ∈ dstarComp (Om R) (tightCore R)

@[expose] def P23E8ZSig (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e →
      u * e ∈ zStarOf (rLayer (Om R) u) → SecAE R e 6 →
        ∀ x : Y, (rLayer (Om R) e).map (MulAut.conj x).toMonoidHom ≠ rLayer (Om R) e →
          rLayer (Om R) e ⊔ (rLayer (Om R) e).map (MulAut.conj x).toMonoidHom ≠ ⊤ →
            ∀ J ∈ dstarComp (Om R) (tightCore R),
              J ≤ rLayer (Om R) e ⊔ (rLayer (Om R) e).map (MulAut.conj x).toMonoidHom

variable {n : ℕ} in
theorem p23E8ZGen_of_parts (hTwo : P23Two n) (hL : P23E8ZLay n) (hS : P23E8ZSig n) : P23E8ZGen n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hz hA6 x hx
  by_contra hne
  have hN := R56.p23_sigmaStarNorm_eq_top_of_layer hc (hTwo Y R S t K' W u e g hc)
    (hL hcit hP Y R S t K' W u e g hc hno hz hA6)
  exact R56.p23_false_of_dstar_proper hc hN (hS hcit hP Y R S t K' W u e g hc hno hz hA6 x hx hne) hne

end E8ZGen

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
