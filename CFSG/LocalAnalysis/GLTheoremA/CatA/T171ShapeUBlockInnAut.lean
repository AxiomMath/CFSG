module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlockResidual
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitzUE
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KL3U3Uni
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterUnitary
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdTorality
import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.Descent
import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.Cover
import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.FamilyProved
import CFSG.HardMathSupport.Seitz.G2Noninner.Descent.OddNeThree
import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.Final
import CFSG.LieType.SeitzGeneration.ExcOuterAssemblyV5
import CFSG.LieType.SeitzGeneration.OmegaF2.Basic
import CFSG.LieType.SeitzGeneration.OuterSpPair
import CFSG.LieType.SeitzGeneration.RootPairOrthBlock
import CFSG.LieType.SeitzGeneration.RootPairSp
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA3pSurvivor
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBS
import CFSG.LocalAnalysis.AGLEmbedding.J3InSitu
import CFSG.LocalAnalysis.AGLEmbedding.J3MSide
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenAssembly
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3FourGenData
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSeitzCyc
import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeightsOne
import CFSG.LocalAnalysis.AGLEmbedding.ReeData
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6G2
import CFSG.LocalAnalysis.RankThreeTheoremC.D1Frontier3
import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLTorus
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorLie
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsThree
import CFSG.RankThree.PartOne.FOCD.G2OddQPlus
import CFSG.RankThree.PartOne.FOCD.PRank
import CFSG.RankThree.PartOne.KC.UnitaryDefining
import CFSG.RankThree.PartOne.SEITZ11.G2OddFinal
import CFSG.RankThree.PartOne.SEITZ7.D4Wire
import CFSG.RankThree.PartOne.SEITZ7.SzPairK
import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofExc
import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofSec19
import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofSec4
import CFSG.RankThree.PartTwo.Sec19.Step1914Split
import CFSG.RankThree.PartTwo.Sec4.E27.Core
import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364
import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzOther
import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzRest
import CFSG.RankThree.PartTwo.Sec4.T444.Item434RowsProofSeitzSz

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Matrix CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (primeFormConjHom_scalar)
open CFSG.ComponentClassification.OuterAutomorphisms

section Helpers

variable {a n : ℕ} {E : Type} [Field E]

private lemma herm_scalar (h : UnitaryFieldData 2 n E) (c : Eˣ) :
    CFSG.StandardType.TableBUD.herm (d := a) n
        (((GeneralLinearGroup.scalar (Fin a) c : GL (Fin a) E)) :
          Matrix (Fin a) (Fin a) E) =
      h.norm (c : E) • (1 : Matrix (Fin a) (Fin a) E) := by
  rw [CFSG.StandardType.TableBUD.herm, GeneralLinearGroup.coe_scalar,
    show Matrix.scalar (Fin a) (c : E) = Matrix.diagonal (fun _ => (c : E)) from rfl,
    TableBUD.map_pow_eq_map_bar h, Matrix.diagonal_map (map_zero h.bar),
    Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, UnitaryFieldData.norm,
    ← Matrix.diagonal_one, ← Matrix.diagonal_smul]
  congr 1
  funext i
  simp [mul_comm]

theorem exists_scalar_mul_primeFormUnitary (h : UnitaryFieldData 2 n E)
    {M : GL (Fin a) E} (hM : M ∈ LargeEvenGUSet (Fin a) E (2 ^ n)) :
    ∃ c : Eˣ, GeneralLinearGroup.scalar (Fin a) c * M ∈
      primeFormUnitary h ((1 : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) := by
  obtain ⟨μ, hμ0, hμq, hμeq⟩ := hM
  have hμF : μ ∈ h.fixedField :=
    (UnitaryFieldData.mem_fixedField h).mpr (by rw [h.bar_apply]; exact hμq)
  obtain ⟨c, hc⟩ := h.normHom_surjective ⟨μ⁻¹, h.fixedField.inv_mem hμF⟩
  have hcval : h.norm c = μ⁻¹ := congrArg Subtype.val hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp only [UnitaryFieldData.norm, map_zero, mul_zero] at hcval
    exact (inv_ne_zero hμ0) hcval.symm
  refine ⟨Units.mk0 c hc0, ?_⟩
  have hcunorm : h.norm ((Units.mk0 c hc0 : Eˣ) : E) = μ⁻¹ := hcval
  rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one, ← TableBUD.map_pow_eq_map_bar h]
  change CFSG.StandardType.TableBUD.herm (d := a) n
    (((GeneralLinearGroup.scalar (Fin a) (Units.mk0 c hc0) * M : GL (Fin a) E)) :
      Matrix (Fin a) (Fin a) E) = 1
  rw [Units.val_mul, TableBUD.herm_mul h, herm_scalar h, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, hμeq, smul_smul, hcunorm, inv_mul_cancel₀ hμ0, one_smul]

private lemma congr_statedProj_projConj (h : UnitaryFieldData 2 n E) (ha : 1 ≤ a)
    (M : GL (Fin a) E) (hN : M ∈ Subgroup.normalizer (unitarySU 2 n E a : Set (GL (Fin a) E)))
    (c : Eˣ)
    (hNunitary : (GeneralLinearGroup.scalar (Fin a) c * M : GL (Fin a) E) ∈
      primeFormUnitary h ((1 : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)) :
    MulAut.congr
        (show LargeEvenProj (unitarySU 2 n E a) ≃* primeFormP h
            ((1 : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) from
          statedProjEquivPrimeFormOne h ha)
        (TableB.projConj (unitarySU 2 n E a) ⟨M, hN⟩) =
      primeFormConjHom h ((1 : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)
        ⟨GeneralLinearGroup.scalar (Fin a) c * M, hNunitary⟩ := by
  set e : LargeEvenProj (unitarySU 2 n E a) ≃* primeFormP h
      ((1 : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) :=
    statedProjEquivPrimeFormOne h ha with he
  refine MulEquiv.ext fun x => ?_
  obtain ⟨y, rfl⟩ := e.surjective x
  induction y using QuotientGroup.induction_on with
  | H g =>
    rw [he]
    change statedProjEquivPrimeFormOne h ha
        (TableB.projConj (unitarySU 2 n E a) ⟨M, hN⟩ (QuotientGroup.mk g)) =
      primeFormConjHom h ((1 : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)
        ⟨GeneralLinearGroup.scalar (Fin a) c * M, hNunitary⟩
        (statedProjEquivPrimeFormOne h ha (QuotientGroup.mk g))
    rw [TableB.projConj_mk, statedProjEquivPrimeFormOne_mk, statedProjEquivPrimeFormOne_mk,
      primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    show (M : GL (Fin a) E) * (g : GL (Fin a) E) * M⁻¹ =
      (GeneralLinearGroup.scalar (Fin a) c * M) * (g : GL (Fin a) E) *
        (GeneralLinearGroup.scalar (Fin a) c * M)⁻¹
    have hpM : GeneralLinearGroup.scalar (Fin a) c * (M : GL (Fin a) E) =
        M * GeneralLinearGroup.scalar (Fin a) c := (commute_scalar c M).eq.symm
    have hpg : GeneralLinearGroup.scalar (Fin a) c * (g : GL (Fin a) E) =
        (g : GL (Fin a) E) * GeneralLinearGroup.scalar (Fin a) c :=
      (commute_scalar c (g : GL (Fin a) E)).eq.symm
    have hpMinv : GeneralLinearGroup.scalar (Fin a) c * (M : GL (Fin a) E)⁻¹ =
        M⁻¹ * GeneralLinearGroup.scalar (Fin a) c :=
      (commute_scalar c (M⁻¹)).eq.symm
    have hX : GeneralLinearGroup.scalar (Fin a) c *
        ((M : GL (Fin a) E) * (g : GL (Fin a) E) * M⁻¹) =
        ((M : GL (Fin a) E) * (g : GL (Fin a) E) * M⁻¹) *
          GeneralLinearGroup.scalar (Fin a) c := by
      calc GeneralLinearGroup.scalar (Fin a) c * ((M : GL (Fin a) E) * g * M⁻¹)
          = (GeneralLinearGroup.scalar (Fin a) c * M) * g * M⁻¹ := by group
        _ = (M * GeneralLinearGroup.scalar (Fin a) c) * g * M⁻¹ := by rw [hpM]
        _ = M * (GeneralLinearGroup.scalar (Fin a) c * g) * M⁻¹ := by group
        _ = M * (g * GeneralLinearGroup.scalar (Fin a) c) * M⁻¹ := by rw [hpg]
        _ = (M * g * M⁻¹) * GeneralLinearGroup.scalar (Fin a) c := by
          rw [show M * (g * GeneralLinearGroup.scalar (Fin a) c) * M⁻¹ =
            M * g * (GeneralLinearGroup.scalar (Fin a) c * M⁻¹) by group, hpMinv]
          group
    calc M * g * M⁻¹
        = (GeneralLinearGroup.scalar (Fin a) c * (M * g * M⁻¹)) *
            (GeneralLinearGroup.scalar (Fin a) c)⁻¹ := by
          rw [hX, mul_inv_cancel_right]
      _ = (GeneralLinearGroup.scalar (Fin a) c * M) * g *
            (GeneralLinearGroup.scalar (Fin a) c * M)⁻¹ := by group

end Helpers

theorem unitaryBlockInnAutDerived_holds : UnitaryBlockInnAutDerived := by
  intro a n E _ _ h p hp hp2 ha hane M hM hN hMp
  obtain ⟨c, hcU⟩ := exists_scalar_mul_primeFormUnitary h hM
  have hNunitary : (GeneralLinearGroup.scalar (Fin a) c * M : GL (Fin a) E) ∈
      primeFormUnitary h ((1 : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) := hcU
  have hcongr := congr_statedProj_projConj h (by omega) M hN c hNunitary
  have hNpow : (GeneralLinearGroup.scalar (Fin a) c * M : GL (Fin a) E) ^ p =
      GeneralLinearGroup.scalar (Fin a) (c ^ p) := by
    rw [(commute_scalar c M).eq.symm, (commute_scalar c M).mul_pow p, hMp, one_mul,
      ← map_pow]
  have hxp : (MulAut.congr
      (show LargeEvenProj (unitarySU 2 n E a) ≃* primeFormP h
          ((1 : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) from
        statedProjEquivPrimeFormOne h (by omega))
      (TableB.projConj (unitarySU 2 n E a) ⟨M, hN⟩)) ^ p = 1 := by
    rw [hcongr, ← map_pow]
    refine primeFormConjHom_scalar h _ _ (c ^ p) ?_
    simpa using hNpow
  have hxD : MulAut.congr
      (show LargeEvenProj (unitarySU 2 n E a) ≃* primeFormP h
          ((1 : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) from
        statedProjEquivPrimeFormOne h (by omega))
      (TableB.projConj (unitarySU 2 n E a) ⟨M, hN⟩) ∈
      primeFormD h ((1 : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) :=
    ⟨⟨GeneralLinearGroup.scalar (Fin a) c * M, hNunitary⟩, hcongr.symm⟩
  have hxinn : MulAut.congr
      (show LargeEvenProj (unitarySU 2 n E a) ≃* primeFormP h
          ((1 : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) from
        statedProjEquivPrimeFormOne h (by omega))
      (TableB.projConj (unitarySU 2 n E a) ⟨M, hN⟩) ∈
      innAutDerived (primeFormP h ((1 : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)) :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.mem_innAutDerived_of_mem_primeFormD h hp hp2 hxD hxp
  exact (mem_innAutDerived_congr (statedProjEquivPrimeFormOne h (by omega))).1 hxinn

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
