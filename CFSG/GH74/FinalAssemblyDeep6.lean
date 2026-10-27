module

public import CFSG.GH74.FinalAssemblyDeep
public import CFSG.GH74.GLS.Stage12.Master
public import CFSG.GH74.GLS.LU.Local.A3
public import CFSG.GH74.GLS.LU.Local.Setup
public import CFSG.GH74.GLS.SP.Local.Setup
public import CFSG.GH74.GLS.Stage4.HexClass
public import CFSG.GH74.Uniqueness.SU.KI6A9Final
public import CFSG.GH74.Uniqueness.SU.KI4Main
public import CFSG.GH74.E2.Alpha1Core
public import CFSG.GH74.E2.CaseIInner
public import CFSG.GH74.E2.OddRank
public import CFSG.GH74.E2.LocalComp
public import CFSG.GH74.E2.DirectProd
public import CFSG.GH74.E2.TermPumpUp
public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms
public import CFSG.GH74.Orders.LieType
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.GH74.GLS.Types
public import CFSG.Open.Catalog
public import CFSG.GH74.E2.LocalLeaves
public import CFSG.GH74.E2.DirectSylow
public import CFSG.GH74.E2.A5Beta
public import CFSG.GH74.E2.A6Inner
public import CFSG.GH74.E2.K0Rest
public import CFSG.GH74.E2.KTables
public import CFSG.GH74.E2.NoM12
public import CFSG.GH74.E2.Ext2
public import CFSG.GH74.E2.Tools
public import CFSG.GH74.E2.SDExtCert
public import CFSG.GH74.E2.SD16Cert
public meta import Mathlib
public meta import CFSG.CharacterTheory.Semidihedral.Model
public import CFSG.Open.StatedDefs
public import CFSG.Blueprint.Catalog
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import CFSG.Open.StatedAPI
public import CFSG.GH74.E2.FactsK
public import CFSG.GH74.E2.AlphaStd
public import CFSG.GH74.E2.A6Outer
public import CFSG.GH74.E2.OuterR1
public import CFSG.GH74.E2.AlphaStdM11
public import CFSG.GH74.E2.Shapes
public import CFSG.GH74.Orders.Sporadic
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.M11Order
public import CFSG.GroupTheory.LocalCores.Components
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Universal.SpecialLinear
public import CFSG.GH74.E2.U5Component
public import CFSG.GH74.E2.BoxB5
public import CFSG.GH74.Generic.S1.GlueUni
public import CFSG.GH74.Generic.S1.GlueLinFull
public import CFSG.GH74.Generic.S1.SymMain
public import CFSG.GH74.Generic.S1.SymNbhd
public import CFSG.GH74.Generic.S1.SymSchur
public import CFSG.GH74.GLS.Stage4.LocalAssembly
public import CFSG.GH74.GLS.Stage4.HexCoord
public import CFSG.GH74.GLS.Stage4.HexCoordD4
public import CFSG.GH74.GLS.Stage12.McLRec
public import CFSG.GH74.E2.BoxFinal13T5
public import CFSG.GH74.Uniqueness.SU.SU12T9
public import CFSG.GH74.GLS.Stage2.Final.ModelSPMain
public import CFSG.GH74.GLS.Stage2.Final.ModelLUMain
public import CFSG.GH74.Uniqueness.SU.KI6Janko
public import CFSG.GH74.Uniqueness.SU.KI1r4Complete
public import CFSG.GH74.GLS.C3.Layer2.L5C20
public import CFSG.GH74.GLS.Stage4.RestCases
public import CFSG.GH74.GLS.LU.Local.Torus8
public import CFSG.GH74.GLS.LU.Local.L3InvAll
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44a
public import CFSG.GH74.GLS.LU.Local.L3Cover
public import CFSG.Milestones.CL_LIT_Walter_abelian_Sylow_two_simple
public import CFSG.GH74.GLS.SP.Local.Gen
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalLSide
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore

public section

namespace CFSG.GH74

open GLS Subgroup Blueprint Assembly.LowTwoRank

theorem walterNativeModels
    : CFSG.Walter.WalterNativeModels :=
  fun G _ _ _ hn P hP => CFSG.Milestones.cl_lit_walter_abelian_sylow_two_simple_models G hn P hP

end CFSG.GH74
