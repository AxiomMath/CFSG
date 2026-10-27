module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusTen
public import CFSG.LocalAnalysis.SteinbergBSEvenSLTwoTorus
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCores
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourStandardAniso
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSetup
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.AUTSL.OmegaFamily
public import CFSG.RankThree.PartOne.AUTSL.Rows
public import CFSG.RankThree.PartOne.AUTSL.SylowTrick
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartOne.S12.Sec1511Y1
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.OmegaMinusLD

open CFSG.Open
open CFSG.SeitzReduction.OmegaPilot
open CFSG.ClassicalGroups.Orthogonal
open QuadraticMap
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open Subgroup

variable {F : Type} [Field F] [Finite F] [CharP F 2] {q : ℕ}
  (b c : F) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

noncomputable abbrev Qc (F : Type) [Field F] (b c : F) : QuadraticForm F (Fin (2 * 5) → F) :=
  coordinateQuadMinus 5 F (by norm_num) b c

@[expose] noncomputable def cPair (F : Type) [Field F] (b c : F) (i : Fin 4) : HypPair (Qc F b c) :=
  (isHypCoord_coordinateQuadMinus (K := F) (n := 5) (by norm_num) b c i).hypPair

theorem cPair_orth (F : Type) [Field F] (b c : F) (i j : Fin 4) (hij : i ≠ j) :
    (cPair F b c i).Orth (cPair F b c j) :=
  (isHypCoord_coordinateQuadMinus (K := F) (n := 5) (by norm_num) b c i).orth
    (isHypCoord_coordinateQuadMinus (K := F) (n := 5) (by norm_num) b c j)
    (pairDisjoint_minus (n := 5) (by norm_num) hij)


theorem exists_order_q_sl2 {n q : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hq : q.Prime) (hqdvd : q ∣ 2 ^ n + 1) :
    ∃ t : Matrix.SpecialLinearGroup (Fin 2) F, orderOf t = q := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 ^ n := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨-, ⟨T, -, hcard⟩, -⟩ :=
    CFSG.LocalAnalysis.SteinbergBS.even_sl2_nonsplit_cyclic_sylow (k := F) (e := n) (by omega) hF'
  have hdvd : q ∣ Nat.card T := by rw [hcard]; exact hqdvd
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) q hdvd
  exact ⟨(t : Matrix.SpecialLinearGroup (Fin 2) F), by simpa using ht⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F.OmegaMinusLD

