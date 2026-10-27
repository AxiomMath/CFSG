module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81Aut
public import CFSG.GH74.GLS.Classes

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def CFTwoNilpSL2 : Prop :=
  ∀ (M : Type) [Group M] [Finite M], IsQuasisimple M → pPrimeCore 2 M = ⊥ →
    Blueprint.Catalog (M ⧸ center M) → (∃ z ∈ center M, orderOf z = 2) →
    ∀ α : MulAut M, α * α = 1 → HasNormalPComplement 2 ↥(fixSub α) →
      (∃ (K' : Type) (_ : Field K') (_ : Finite K') (r m : ℕ), r.Prime ∧ r ≠ 2 ∧ 1 ≤ m ∧
          Nat.card K' = r ^ m ∧ 5 ≤ r ^ m ∧
          Nonempty (M ≃* Matrix.SpecialLinearGroup (Fin 2) K')) ∨
        GH74.GLS.IsDoubleCoverOfAlt M 7 ∨ Blueprint.LieModel (M ⧸ center M) .PSL 3 2 2 ∨
        ¬ 3 ∣ Nat.card M

end CFSG.ComponentClassification.GSThmB
