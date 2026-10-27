module

public import CFSG.ClassicalInvolution.Generic.Induction

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts.L6C

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable (p : ℕ) [Fact p.Prime]

@[expose] def Aut164L4 : Prop :=
  ∀ (e : ℕ), StatedLieAdmissible .PSL 4 p e → p ^ e % 4 = 3 →
    ∀ (Y : Type) [Group Y] (ψ : (modelUniv .PSL 4 p e Fact.out).K →* Y),
      ψ.ker ≤ Subgroup.center (modelUniv .PSL 4 p e Fact.out).K → Function.Surjective ψ →
        ∀ β : MulAut Y, β ^ 2 = 1 →
          ∃ R ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 p e Fact.out).D, ∃ s ∈ R,
            orderOf (ψ s) = 4 ∧ β (ψ s) = ψ s

@[expose] def Aut164U4 : Prop :=
  ∀ (e : ℕ), StatedLieAdmissible .PSU 4 p e → p ^ e % 4 = 1 →
    ∀ (Y : Type) [Group Y] (ψ : (modelUniv .PSU 4 p e Fact.out).K →* Y),
      ψ.ker ≤ Subgroup.center (modelUniv .PSU 4 p e Fact.out).K → Function.Surjective ψ →
        ∀ β : MulAut Y, β ^ 2 = 1 →
          ∃ R ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 p e Fact.out).D, ∃ s ∈ R,
            orderOf (ψ s) = 4 ∧ β (ψ s) = ψ s

end CFSG.ClassicalInvolution.ModelFacts.L6C
