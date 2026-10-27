module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallGraph4Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLGraphKill
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallClass

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.CatalogueBGraphForm (pureGraphAction)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBLinearHigherB
open CFSG.ComponentClassification.CatalogueBHigherLinearAction

theorem a6_psl_pureGraph_small_four (hO : LieOrderFormulasInput) {f : ℕ} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 3 ^ f) (hs : A6Shape .PSL 4 f) (A : GL (Fin 4) K)
    (hsigma : orderOf (pureGraphAction 4 K A) = 2)
    (D : Subgroup ↥(fixedSubgroup (pureGraphAction 4 K A)))
    (hD : A6Hyp (pureGraphAction 4 K A) D) :
    A6SmallConcl .PSL 4 f (pureGraphAction 4 K A) D := by
  have hf : f = 1 := by
    rcases hs with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩ | h | h | h | h | h | h
    · omega
    · omega
    · exact h
    all_goals exact absurd h.1 (by decide)
  subst hf
  have hK3 : Nat.card K = 3 := by simpa using hK
  have hodd : Odd (Nat.card K) := by rw [hK3]; decide
  have hodd' := CatalogueBHigherLinearInner.ringChar_ne_two_of_odd_card K hodd
  have htwo : (2 : K) ≠ 0 := Ring.two_ne_zero hodd'
  by_cases hin : pureGraphAction 4 K A ∈ (MulAut.conj : ProjectiveSpecialLinearGroup (Fin 4) K →*
      MulAut (ProjectiveSpecialLinearGroup (Fin 4) K)).range
  ·
    obtain ⟨B, hB⟩ := PSLSmall.exists_innerDiagonal_of_mem_range hin
    have hσB : orderOf (innerDiagonalAction 4 K B) = 2 := hB ▸ hsigma
    exact PSLSmall.SmallStmt.of_eq hB
      (fun D' hD' => PSLSmall.smallConcl_of_big (PSLSmall.inner_four_big hK3 htwo hσB hD')) D hD
  · suffices hev : PSLSmall.OuterEvidence (pureGraphAction 4 K A) from
      PSLSmall.smallConcl_of_evidence hD hev (fun h => absurd h hin)
    have hsq2 : pureGraphAction 4 K A ^ 2 = 1 := by
      have := pow_orderOf_eq_one (pureGraphAction 4 K A)
      rwa [hsigma] at this
    have hform := CatalogueBGraphForm.pureGraph_involution_form_data 4 K (by norm_num) hodd' A hsq2
    obtain ⟨hDc, hDZ⟩ := hD.component
    obtain ⟨N, hN, ⟨eDN⟩⟩ := pureGraph_component_transfer A hDc
    have hNA : Nonempty (N ⧸ center N ≃* alternatingGroup (Fin 6)) := ⟨eDN.symm.trans hDZ.some⟩
    have hdim : Module.finrank K (Fin 4 → K) = 4 := by rw [Module.finrank_fin_fun]
    rcases hform with hsymm | ⟨halt, -⟩
    · by_cases hS : ∃ S : Submodule K (Fin 4 → K), Module.finrank K S = 2 ∧
          ∀ x ∈ S, matrixQuadraticForm A⁻¹ x = 0
      ·
        exfalso
        have hR := transpose_inv_of_transpose_eq A hsymm
        have hQ₀ : (matrixQuadraticForm A⁻¹).polarBilin.Nondegenerate :=
          polarBilin_matrixQuadraticForm_nondegenerate hodd' A⁻¹ hR
        let e₁ : ↥(CatalogueBGraphForm.isometryGroup 4 K A⁻¹) ≃*
            ↥(TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm A⁻¹)) :=
          (isometryGroupEquiv A⁻¹).symm.trans
            (MulEquiv.subgroupCongr (orthogonalGroup_matrixQuadraticForm hodd' A⁻¹ hR).symm)
        have hN₀ : IsComponent (N.map e₁.toMonoidHom) := LocalCores.isComponent_map_mulEquiv e₁ hN
        haveI : Group.IsSolvable
            ↥(TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm A⁻¹)) :=
          ((CatalogueBOrthogonalLowDimensionFrontiers.orthogonal_four_split_p_components_frontier
            hodd (matrixQuadraticForm A⁻¹) hQ₀ hdim hS).2 hK3).1
        exact CatLeafProof.not_isComponent_of_isSolvable hN₀
      · exact PSLSmall.Graph4.nonsplit_evidence hK3 A hsymm hS
    ·
      exfalso
      have hR := transpose_inv_of_transpose_eq_neg A halt
      let eI := isometryGroupEquiv A⁻¹
      have hN' : IsComponent (N.map eI.symm.toMonoidHom) :=
        LocalCores.isComponent_map_mulEquiv eI.symm hN
      have hNA' : Nonempty (↥(N.map eI.symm.toMonoidHom) ⧸ center ↥(N.map eI.symm.toMonoidHom) ≃*
          alternatingGroup (Fin 6)) :=
        ⟨(centerQuotient_map_equiv eI.symm N).some.symm.trans hNA.some⟩
      have hmodel := CatLeafProof.X10Sp.centralModel_isometryGroup_component (ℓ := 3) (j := 1)
        (m := 2) Nat.prime_three (by norm_num) (by norm_num) (by simpa using hK3)
        (matrixForm A⁻¹) (matrixForm_isAlt hodd' A⁻¹ hR) (matrixForm_nondegenerate A⁻¹)
        (by rw [Module.finrank_fin_fun]) le_rfl hN'
      have h := a6sq_lieModel_a6 hO hNA' hmodel.1 (by norm_num) hmodel.2
      exact absurd h.1 (by decide)

end CFSG.ComponentClassification.CatFC
