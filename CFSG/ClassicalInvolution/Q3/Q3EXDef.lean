module

public import CFSG.ClassicalInvolution.RouteD.ExoticTwinModel
public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD.Exotic

@[expose] def MFTwin3 : Prop :=
  ∀ (t : StatedLieTag) (n a : ℕ), IsFundTag t → t ≠ .G2 → t ≠ .trialityD4 →
    StatedLieAdmissible t n 3 1 → ¬ (t = .PSL ∧ n = 2) → 2 ≤ a → ModelTwinClass 3 t n 1 a →
    CoreAssembly.ShapeTable a t n ∨ (t = .POmegaPlus ∧ n = 4 ∧ a ≤ 4)

end CFSG.ClassicalInvolution.Q3.Q3W
