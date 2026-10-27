module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166FamF4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Mult
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Build
public import CFSG.LocalAnalysis.StandardType.GGTableBF4EndNode
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotToral
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCentralizerTUStd
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.EntryLemma
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExc
public import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
public import CFSG.Assembly.LargeEvenGLABridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.SplitCore
public import CFSG.Assembly.OpenBridges
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.StandardType CFSG.StandardType.TableBF4 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot

section Certs


theorem hasLabel_c3Levi {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 1 ≤ n) : HasLabel ↥(C3Levi F) (· = ⟨.B, 3, n⟩) := by
  haveI : CharP F 2 := charP_two_of_natCard_eq_two_pow hF
  have hmodel : CFSG.Blueprint.LieModel ↥(C3Levi F) .PSp 3 2 n := lieModel_C3Levi hF
  have hSC : StatedClassicalModel ↥(C3Levi F) .PSp 3 2 n :=
    hmodel.statedClassicalModel (by decide : StatedLieTag.PSp ∈ classicalTags)
  have hZ : Subgroup.center ↥(C3Levi F) = ⊥ := center_C3Levi_eq_bot
  let eZ : ↥(C3Levi F) ⧸ Subgroup.center ↥(C3Levi F) ≃* ↥(C3Levi F) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact hasLabel_of_statedClassicalModel_PSp (isQuasisimple_C3Levi (K := F))
    (CFSG.CGT.Timmesfeld75.statedClassicalModel_of_mulEquiv eZ.symm hSC)

theorem hasLabel_adjointGroup_F4 {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) :
    HasLabel (adjointGroup .F4 F) (· = ⟨.F4, 0, n⟩) := by
  have hlab : GLAInLambda2 ⟨.F4, 0, n⟩ := ⟨hn, rfl⟩
  refine hasLabel_of_quasisimple_rawDatum
    (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 (K := F)) hlab ?_
  refine ⟨F, inferInstance, inferInstance, hF, ?_⟩
  let eZ : adjointGroup .F4 F ⧸ Subgroup.center (adjointGroup .F4 F) ≃*
      adjointGroup .F4 F :=
    (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := .F4) (K := F))).trans
      QuotientGroup.quotientBot
  exact ⟨eZ.trans (recipeChevEquiv .F4 F).symm⟩

theorem evenRank_adjointGroup_F4 {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) : evenRank (adjointGroup .F4 F) = 4 := by
  have hn1 : 1 ≤ n := by omega
  have hlab := hasLabel_adjointGroup_F4 hF hn1
  have hK : Rk2IsLabel (adjointGroup .F4 F) ⟨.F4, 0, n⟩ := hlab
  exact le_antisymm (evenRank_le_four_of_F4 hK rfl) (rk2_low_f4 _ _ hK rfl hn)

theorem endNode_comp {F : Type} [Field F] [Finite F] [CharP F 2] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {ζ : Fˣ} (hζo : orderOf ζ = q) :
    IsComponentOf (C3Levi F) (Subgroup.centralizer ({endNodeElt F ζ} : Set (adjointGroup .F4 F))) ∧
      GLALayer (Subgroup.centralizer ({endNodeElt F ζ} : Set (adjointGroup .F4 F))) = C3Levi F := by
  have h3 : 3 ≤ orderOf ζ := by
    rw [hζo]
    exact lt_of_le_of_ne hq.two_le (Ne.symm hq2)
  have hchar : ringChar F = 2 := ringChar.eq F 2
  obtain ⟨hlay, hcomp⟩ := layer_centralizer_endNodeElt (K := F) hchar h3
  refine ⟨(CFSG.Assembly.isComponentOf_iff_open).1 hcomp, ?_⟩
  rw [← CFSG.Assembly.LargeEven.largeEvenLayer_eq_glaLayer]
  exact hlay


end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
