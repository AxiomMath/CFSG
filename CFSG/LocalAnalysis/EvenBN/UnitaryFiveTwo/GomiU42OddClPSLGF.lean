module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClComp
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinField

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.CatalogueBGraphField (graphFieldAction)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem u42_psl_graphField (hO : LieOrderFormulasInput) {n f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ^ f) (hn : 3 ≤ n) (hadm : StatedLieAdmissible .PSL n 3 f)
    (A : GL (Fin n) K) (σ : K ≃+* K) (hσ1 : σ ≠ 1)
    (hord : orderOf (graphFieldAction n K A σ) = 2)
    {J : Subgroup ↥(fixedSubgroup (graphFieldAction n K A σ))}
    (hJ : U42Hyp (graphFieldAction n K A σ) J) : False := by
  obtain ⟨j, -, hadm', hmodel⟩ :=
    CFSG.ComponentClassification.CatLeafProof.X10Lin.graphField_psl_component_model (p := 3) hn
      Nat.prime_three (by norm_num) hadm.2.1 hK A σ hσ1 hord
      (X := ↥(fixedSubgroup (graphFieldAction n K A σ))) (MulEquiv.refl _) hJ.isComponent
  have h := u42_lieModel_card_25920 hO hadm' hmodel hJ.card_centerQuotient
  exact absurd h.1 (by decide)

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
