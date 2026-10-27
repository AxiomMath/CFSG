module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Witness
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinField

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.CatalogueBGraphField (graphFieldAction)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem a6_psl_graphField (hO : LieOrderFormulasInput) {n f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ^ f) (hn : 3 ≤ n) (hadm : StatedLieAdmissible .PSL n 3 f)
    (hm : LieModel (ProjectiveSpecialLinearGroup (Fin n) K) .PSL n 3 f)
    (A : GL (Fin n) K) (σ : K ≃+* K) (hσ1 : σ ≠ 1)
    (hord : orderOf (graphFieldAction n K A σ) = 2)
    (D : Subgroup ↥(fixedSubgroup (graphFieldAction n K A σ)))
    (hD : A6Hyp (graphFieldAction n K A σ) D) : False := by
  clear hm
  obtain ⟨hDc, hDZ⟩ := hD.component
  obtain ⟨j, -, hadm', hmodel⟩ :=
    CatLeafProof.X10Lin.graphField_psl_component_model (p := 3) hn Nat.prime_three
      (by norm_num) hadm.2.1 hK A σ hσ1 hord
      (X := ↥(fixedSubgroup (graphFieldAction n K A σ))) (MulEquiv.refl _) hDc
  have h := a6sq_lieModel_a6 hO hDZ hadm' (by norm_num) hmodel
  exact absurd h.1 (by decide)

end CFSG.ComponentClassification.CatFC
