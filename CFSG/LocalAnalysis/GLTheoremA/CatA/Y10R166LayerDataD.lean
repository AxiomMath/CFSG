module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutDescent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerSymplecticOrth
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open Subgroup CFSG.Open
open CFSG.SeitzReduction.OmegaPilot
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus plusIndexEquiv
  regular_coordinateQuadPlus commutator_coordinateQuadPlus)

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem isQuasisimple_center_coordinatePlus {m : ℕ} (hm : 3 ≤ m) :
    CFSG.IsQuasisimple (matrixProjectiveDerived (coordinateQuadPlus m F)) ∧
      Subgroup.center (matrixProjectiveDerived (coordinateQuadPlus m F)) = ⊥ := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus m F hm
  obtain ⟨hs, hnab⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonalSubfield.matrix_simple_nonabelian (by omega : 0 < 2 * m) hQ hT
  haveI : IsSimpleGroup (matrixProjectiveDerived (coordinateQuadPlus m F)) := hs
  exact CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab

theorem hasLabel_coordinatePlus (m n : ℕ) (hF : Nat.card F = 2 ^ n) (hm : 4 ≤ m)
    (hn : 2 ≤ n) :
    HasLabel (matrixProjectiveDerived (coordinateQuadPlus m F)) (· = ⟨.D, m, n⟩) := by
  obtain ⟨hQ, hZ⟩ := isQuasisimple_center_coordinatePlus (F := F) (m := m) (by omega)
  have hSC : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus m F))
      .POmegaPlus m 2 n :=
    CFSG.SeitzReduction.E7Pilot.statedClassicalModel_coordinatePlus (F := F) (n := m) (f := n)
      (by omega) hF hm
  have hSC' : StatedClassicalModel
      (matrixProjectiveDerived (coordinateQuadPlus m F) ⧸
        Subgroup.center (matrixProjectiveDerived (coordinateQuadPlus m F))) .POmegaPlus m 2 n :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm hSC
  exact hasLabel_of_statedClassicalModel_POmegaPlus hQ hSC'

theorem hasLabel_pairPerp {m n : ℕ} (hF : Nat.card F = 2 ^ n) (hm : 5 ≤ m)
    (hn : 2 ≤ n) (k : Fin m) :
    HasLabel ↥(pairPerp (K := F) (n := m) k) (· = ⟨.D, m - 1, n⟩) := by
  have hM : CFSG.Blueprint.LieModel ↥(pairPerp (K := F) (n := m) k) .POmegaPlus (m - 1) 2 n :=
    lieModel_pairPerp (K := F) (n := m) hF hm k
  have hSC : StatedClassicalModel ↥(pairPerp (K := F) (n := m) k) .POmegaPlus (m - 1) 2 n :=
    hM.statedClassicalModel (by decide)
  have hq : CFSG.IsQuasisimple ↥(pairPerp (K := F) (n := m) k) :=
    isQuasisimple_pairPerp (K := F) (by omega) k
  have hZ : Subgroup.center ↥(pairPerp (K := F) (n := m) k) = ⊥ :=
    center_pairPerp (K := F) (n := m) (by omega) k
  have hSC' : StatedClassicalModel
      (↥(pairPerp (K := F) (n := m) k) ⧸
        Subgroup.center ↥(pairPerp (K := F) (n := m) k)) .POmegaPlus (m - 1) 2 n :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm hSC
  exact hasLabel_of_statedClassicalModel_POmegaPlus hq hSC'

section LabelToModel

theorem exists_mulEquiv_matrixProjectiveDerived_of_isLabel {K : Type} [Group K] [Finite K]
    {m n : ℕ} (hm : 4 ≤ m) (hn : 2 ≤ n)
    (hK : HasLabel K (· = ⟨.D, m, n⟩)) (hZ : Subgroup.center K = ⊥) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ n ∧ Nonempty (K ≃* matrixProjectiveDerived (coordinateQuadPlus m F)) := by
  obtain ⟨-, -, hM⟩ := quasisimple_markedModel_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .POmegaPlus m 2 n := by
    simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
      CFSG.StandardType.markRank, CFSG.StandardType.markChar, CFSG.StandardType.markDeg,
      if_neg (by omega : m ≠ 3)] using hM
  obtain ⟨-, F, hfield, hfinite, hcard, ⟨e⟩⟩ := hM'.statedClassicalModel (by decide)
  letI : Field F := hfield
  letI : Finite F := hfinite
  haveI : Fintype F := Fintype.ofFinite F
  have hcard' : Fintype.card F = 2 ^ n := by rwa [← Nat.card_eq_fintype_card]
  have hchar : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  letI : CharP F 2 := hchar
  refine ⟨F, hfield, hfinite, hchar, hcard, ⟨?_⟩⟩
  let eZ : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  exact eZ.trans (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinatePlusWitnessEquiv
    (H := K ⧸ Subgroup.center K) (n := m) F e)

end LabelToModel

end CFSG.LocalAnalysis.GLTheoremA.Y10F
