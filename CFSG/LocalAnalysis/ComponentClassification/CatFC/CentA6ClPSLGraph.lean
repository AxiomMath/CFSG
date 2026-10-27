module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLGraphKill
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinGraph

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.CatalogueBGraphForm (pureGraphAction)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem psl_two_two_mem_graphTuples {n f : ℕ}
    (h : ((.PSL : StatedLieTag), 2, 2) ∈ CatLeafProof.X10Lin.graphTuples n f) :
    (n = 3 ∧ f = 2) ∨ (n = 4 ∧ f = 1) ∨ (n = 4 ∧ f = 2) := by
  simp [CatLeafProof.X10Lin.graphTuples, CatLeafProof.X10Lin.orthTuples] at h
  omega

theorem a6_psl_pureGraph (hO : LieOrderFormulasInput) {n f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ^ f) (hn : 3 ≤ n) (hadm : StatedLieAdmissible .PSL n 3 f)
    (hm : LieModel (ProjectiveSpecialLinearGroup (Fin n) K) .PSL n 3 f) (A : GL (Fin n) K)
    (hσ : orderOf (pureGraphAction n K A) = 2)
    (D : Subgroup ↥(fixedSubgroup (pureGraphAction n K A)))
    (hD : A6Hyp (pureGraphAction n K A) D) : A6Shape .PSL n f := by
  clear hadm hm
  obtain ⟨hDc, hDZ⟩ := hD.component
  obtain ⟨t, n', e', hT, hadm', hmodel⟩ :=
    CatLeafProof.X10Lin.graph_psl_component_models Nat.prime_three (by norm_num) hK hn A hσ hDc
  obtain ⟨rfl, rfl, -, rfl⟩ := a6sq_lieModel_a6 hO hDZ hadm' (by norm_num) hmodel
  rcases psl_two_two_mem_graphTuples hT with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  · exact (a6_pureGraph_not_four_two hO hK A hσ D hD).elim

end CFSG.ComponentClassification.CatFC
