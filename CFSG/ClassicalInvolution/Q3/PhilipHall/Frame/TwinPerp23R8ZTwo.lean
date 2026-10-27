module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section E8ZTwo

@[expose] def P23E8ZTwo (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e →
      u * e ∈ zStarOf (rLayer (Om R) u) → SecAE R e 6 →
        ∃ y : Y, y * t = t * y ∧ y * e = e * y ∧ y * y = 1 ∧
          (∀ l ∈ tightCore R ⊔ K', y * l * y⁻¹ * l⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y))) ∧
          ∃ ρ : ↥(Subgroup.closure ({e, t, y} : Set Y) ⊔ rLayer (Om R) e) →* Equiv.Perm (Fin 6),
            Function.Surjective ρ ∧
            ρ.ker ≤ (rLayer (Om R) e).subgroupOf (Subgroup.closure ({e, t, y} : Set Y) ⊔ rLayer (Om R) e)

end E8ZTwo

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
