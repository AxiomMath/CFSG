module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUniBlockHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUniBlockHoldsTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUniBlockHoldsPaired
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUniBlockHoldsSelfDual
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInUniTransPow
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeCases

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S171
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
open scoped commutatorElement


theorem uniBlockInnDiag_holds : UniBlockInnDiag := by
  intro G _ _ p L J A d b N n K _ _ hfield hN hNq hS θ D B hDgu hBgu hDN hBN hDp hcomm hDind hBind
  classical
  obtain ⟨σD, hDσ⟩ := CFSG.StandardType.TableBU63.exists_unitary_of_gu hfield hDgu
  obtain ⟨σB, hBσ⟩ := CFSG.StandardType.TableBU63.exists_unitary_of_gu hfield hBgu
  set A' : GL (Fin N) K := Matrix.GeneralLinearGroup.scalar (Fin N) σD * D with hA'def
  set C' : GL (Fin N) K := Matrix.GeneralLinearGroup.scalar (Fin N) σB * B with hC'def
  have hA' : A' ∈ primeFormUnitary hfield (idGram K N) := hDσ
  have hC' : C' ∈ primeFormUnitary hfield (idGram K N) := hBσ
  have hA'N : A' ∈ Subgroup.normalizer (unitarySU 2 n K N : Set (GL (Fin N) K)) :=
    CFSG.StandardType.SUTorus.mem_normalizer_of_mem_primeFormUnitary hfield hA'
  have hC'N : C' ∈ Subgroup.normalizer (unitarySU 2 n K N : Set (GL (Fin N) K)) :=
    CFSG.StandardType.SUTorus.mem_normalizer_of_mem_primeFormUnitary hfield hC'
  have hcomm' : Commute A' C' := by
    have h1 : ⁅A', C'⁆ = 1 := by
      rw [show A' = Matrix.GeneralLinearGroup.scalar (Fin N) σD * D from rfl,
        show C' = Matrix.GeneralLinearGroup.scalar (Fin N) σB * B from rfl]
      rw [CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center
        (Subgroup.mem_center_iff.2 fun x =>
          (Matrix.GeneralLinearGroup.scalar_commute σD x).symm)
        (Subgroup.mem_center_iff.2 fun x =>
          (Matrix.GeneralLinearGroup.scalar_commute σB x).symm) D B]
      exact commutatorElement_eq_one_iff_commute.mpr hcomm
    exact commutatorElement_eq_one_iff_commute.mp h1
  have hA'p : ∃ c : Kˣ, A' ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) c :=
    ⟨σD ^ p, by
      rw [show A' = Matrix.GeneralLinearGroup.scalar (Fin N) σD * D from rfl]
      exact (CFSG.HardMathSupport.Timmesfeld.CrossChar.scalar_mul_pow σD D p).trans
        (by rw [hDp, mul_one])⟩
  have hD'proj : TableB.projConj (unitarySU 2 n K N) ⟨A', hA'N⟩ =
      TableB.projConj (unitarySU 2 n K N) ⟨D, hDN⟩ :=
    projConj_scalar_mul (unitarySU 2 n K N) σD D hDN hA'N
  have hC'proj : TableB.projConj (unitarySU 2 n K N) ⟨C', hC'N⟩ =
      TableB.projConj (unitarySU 2 n K N) ⟨B, hBN⟩ :=
    projConj_scalar_mul (unitarySU 2 n K N) σB B hBN hC'N
  have hDind' : LargeEvenInduces θ (conjRel d)
      (TableB.projConj (unitarySU 2 n K N) ⟨A', hA'N⟩) := by
    rw [hD'proj]; exact hDind
  have hCind' : LargeEvenInduces θ (conjRel b)
      (TableB.projConj (unitarySU 2 n K N) ⟨C', hC'N⟩) := by
    rw [hC'proj]; exact hBind
  have hdp : d ^ p = 1 := hS.elem.2 d hS.d_mem
  have hbp : b ^ p = 1 := hS.elem.2 b hS.b_mem
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag hS.d_mem
  have hbN : b ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag hS.b_mem
  have hres := uniJ_equiv_comm hS.prime hS.odd hdp hdN hbN hS.pcomp hS.b_norm hfield hN hNq
    θ A' C' hA' hC' hA'N hC'N hA'p hcomm' hDind' hCind'
  have hq : CFSG.IsQuasisimple (PQuot p J) :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff (PQuot p J)).2.2.1.mpr
      (isQuasisimple_pQuot_of_glaPComponent hS.prime hS.pcomp)
  rcases hres with hself | hpair
  · obtain ⟨m, E, instE, finE, k, hE, B₁, hB₁, hconj, e₀, hm2, hk2, hk3, he₀⟩ := hself
    letI : Field E := instE
    letI : Finite E := finE
    by_cases hm3 : 3 ≤ m
    · exact innDiagOn_of_uniJSelfDualModel_three_le hS.prime hS.odd hS.b_norm hq hbp
        hE B₁ hB₁ hconj e₀ he₀ hm3 hk3
    · have hm : m = 2 := by omega
      exact innDiagOn_of_uniJSelfDualModel_two hS.prime hS.odd hS.b_norm hq hbp
        hE B₁ hB₁ hconj e₀ he₀ hm (hk2 hm)
  · exact innDiagOn_of_uniJPairedModel hS.prime hS.odd hS.b_norm hq hbp hpair

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
