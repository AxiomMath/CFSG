module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Model

public section

namespace CFSG.ClassicalInvolution.Asc77.S24

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

@[expose] def FactFG0C : Prop :=
  ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 5 ≤ p ^ e →
    ∀ (E : Type) [Group E] [Finite E] [IsSimpleGroup E] (Ω : Set (Subgroup E))
      (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k e' : ℕ),
        ((t = .G2 ∧ k = 0) ∨ (t = .trialityD4 ∧ k = 0)) → Nonempty (Ih8Model p e Ω t k e') →
        ∀ L ∈ Ω, ∃ (F : Type) (_ : Field F) (_ : Fintype F),
          Nonempty (↥(Subgroup.centralizer (L : Set E)) ≃* SL(2, F))

end CFSG.ClassicalInvolution.Asc77.S24
