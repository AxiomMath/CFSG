module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTop
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aSelfDualRank

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped MatrixGroups Matrix

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.X7
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem squareFiltrationExhaustion :
    ∀ (f : ℕ) (F : Type) [Field F] [Fintype F] [CharP F 2], 1 ≤ f → Fintype.card F = 2 ^ f →
      ∀ (k : Type) [Field k] [Algebra F k] [CharP k 2] (W : Type) [AddCommGroup W] [Module k W]
        [Module.Finite k W] (ρ : Representation k SL(3, F) W), ρ.IsIrreducible →
          ∃ a b : Fin f → Bool, Nonempty (ρ.Equiv (matRep (tensorRep (F := F) k a b))) := by
  intro f F _ _ _ hf hF k _ _ _ W _ _ _ ρ hρ
  obtain ⟨a, b, ⟨e⟩⟩ := exists_T3_equiv k hF hf ρ hρ
  exact ⟨a, b, ⟨e.symm⟩⟩

theorem noPSL3Component_final (h9 : ActualLinearThreeSelfDualSections) :
    CFSG.QuasithinUnique.Setup.Top.NoPSL3Component :=
  noPSL3Component selfDualInvolutionRank h9

end CFSG.QuasithinUnique.Setup.X7a
