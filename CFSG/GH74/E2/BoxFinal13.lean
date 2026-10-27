module

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
public import CFSG.GH74.E2.BoxT5
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.GH74.GLS.TwoThin.G.Section
public import CFSG.GH74.GLS.TwoThin.KGroupCore
public import CFSG.GH74.KGroups.L28Tables
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

namespace CFSG.GH74.E2

open CFSG.GH74.Generic

theorem s_restrictedEvenThin_final13
    (hGKF : GenericKnownFacts)
    (hT5 : Box.AschbacherTheorem5Statement) (hAS : AschbacherStandardL33)
    (hASM : AschbacherStandardM11) : S_restrictedEvenThin :=
  have hD : K0Data := k0Data_of_rest (k0DataRest_of_rest2 k0Rest2)
  have hD3 : K0Data3 := k0Data3_of_rest (k0Data3Rest_of_rest2 k0Rest2)
  have hP : PumpUpData := pumpUpData_of_rest2 k0Rest2
  have hComp : ComponentList := evenType_components hGKF e2ComponentFacts hD
  have hGL : NoLocalGL23 := Box.noLocalGL23_T5 hT5 hAS hASM hComp hD hD3 hP m11Tables l33Tables
  have hA6o : NoLocalA6Outer := noLocalA6Outer_of_tables hComp hP
  have hOut : NoLocalL33Outer := noLocalL33Outer_final hComp hD3 l33Tables
  have hA6 : NoLocalA6 := noLocalA6_of hComp hD3 hP hA6o
  have hI : NoCaseI :=
    noCaseI_of hComp hD hD3 q8Lemma
      (noCaseIQ8_of_shapes (noCaseIA6_of hA6)
        (noCaseIL33_of hComp hD3 m11Tables l33Tables hGL hOut)
        (noCaseIM11_of hComp hD3 m11Tables l33Tables hGL))
  s_restrictedEvenThin_of_localLeaves' hGKF e2ComponentFacts hD hD3 hP
    (pumpUpData2_of_rest2 k0Rest2) m11Tables l33Tables (NoM12.noComponent2M12_of hComp) hA6 hOut
    hGL (noCaseIIAlphaL33_of_standard hComp hP hD3 hI hAS)
    (noCaseIIAlphaM11_of_standard hComp hP hD3 hI hASM)

end CFSG.GH74.E2
