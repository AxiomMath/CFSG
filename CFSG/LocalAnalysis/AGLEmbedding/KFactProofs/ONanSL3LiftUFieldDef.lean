module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

@[expose] def SubfieldDiagGen {p f : ℕ} {K : Type} [Field K] (_h : UnitaryFieldData p f K)
    (K₀ : Subfield K) : Prop :=
  ∀ H : Subgroup (unitarySU p f K 3),
    (∀ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ K₀) → g ∈ H) →
    (∀ g : unitarySU p f K 3, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag → g ∈ H) →
      H = ⊤

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField
