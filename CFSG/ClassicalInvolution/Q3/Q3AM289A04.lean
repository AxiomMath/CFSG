module

public import CFSG.ClassicalInvolution.Q3.Q3T8E4Gen

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace S3A

section Tag


variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem tag3_of_not_dConnected {n : ℕ} (hn : CITBelowT (.sl2 3 1) n) (hih : IH8T 3 1 n)
    (hlt : Nat.card X < n) (hΦ : HypOmegaModU (.sl2 3 1) Φ) (hO : classicalInvolutionOddCore X = ⊥)
    (hgen : omegaGen Φ = ⊤) (hA : ∀ L ∈ Φ, AEmpty Φ L) (hdisc : ¬ DConnected Φ)
    {A B : Subgroup X} (hAΦ : A ∈ Φ) (hB : B ∈ omegaNbr Φ A) :
    ∃ (t : StatedLieTag) (k : ℕ), ((t = .PSp ∧ k = 2) ∨ (t = .PSL ∧ k = 4) ∨ (t = .PSU ∧ k = 4) ∨
      (t = .POmegaOdd ∧ k = 3) ∨ (t = .POmegaPlus ∧ k = 4) ∨ (t = .POmegaMinus ∧ k = 4)) ∧
      Nonempty (Ih8Model 3 1 Φ t k 1) :=
  E4G3.e4_tag3D hn hih hlt hΦ hO hgen hA hdisc hAΦ hB

end Tag

end S3A

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
