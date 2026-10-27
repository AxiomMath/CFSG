module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting

public section

namespace CFSG.ComponentClassification.OutcomeLocal

open CFSG.Blueprint

@[expose] def UOutcome (X : Type) [Group X] : Prop :=
  OddLieType (GeneralizedFitting.subgroup X) ∨
    (∃ n : ℕ, Odd n ∧ 7 ≤ n ∧
      Nonempty (GeneralizedFitting.subgroup X ≃* alternatingGroup (Fin n)) ∧
      (n % 4 = 1 → GeneralizedFitting.subgroup X < ⊤)) ∨
    ((LieModel (GeneralizedFitting.subgroup X) .PSL 3 2 2 ∨
        Nonempty (GeneralizedFitting.subgroup X ≃* NativeSporadic.He)) ∧
      GeneralizedFitting.subgroup X < ⊤)

end CFSG.ComponentClassification.OutcomeLocal
