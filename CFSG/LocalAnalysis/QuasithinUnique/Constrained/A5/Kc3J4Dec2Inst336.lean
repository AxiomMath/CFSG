module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2CertB
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B336Data
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2Native
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B336Data
public import Certificates.Certificate4002
public import Certificates.Certificate4003
public import Certificates.Certificate4004
public import Certificates.Certificate4008
public import Certificates.Certificate4014
public import Certificates.Certificate4016
public import Certificates.Certificate4017
public import Certificates.Certificate4024
public import Certificates.Certificate4025
public import Certificates.Certificate4027
public import Certificates.Certificate4118
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Inv
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2Core
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4FinalBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4HBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Parts
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2_4_27
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3StructureBasic
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.C1GNInputs
public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.Quasithin.EmptyFaithful.QTKELocal
public import CFSG.Sporadic.J4.QT2LocEInterBase
public import CFSG.Sporadic.J4.QT2LocFixMain
public import CFSG.Sporadic.J4.QT2LocMain
public import CFSG.Sporadic.J4.QT2LocMainBase
public import CFSG.Sporadic.J4.QT2LocRadMain
public import CFSG.Sporadic.J4.QT2LocUniq
public import CFSG.Sporadic.J4.QTOutChar
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import Certificates.Certificate43

public section

namespace CFSG.QuasithinUnique.A5.Dec2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4.QT2

theorem chkAll_B336 : chkAll wsB336 (etaE 1) = true :=
  Certificates.certificate4118

theorem classRad_B336 (hF : J4Basic) (hK0 : Subgroup.centralizer ({fiveElt} : Set J) ≤ X0Sub) :
    ClassRad (Vgrp wsB336) :=
  classRad_of_chkAll_b hF hK0 (q := eta uJ 11 1) (Mx_eta hF.mat 11 le_rfl 1) chkAll_B336

end CFSG.QuasithinUnique.A5.Dec2
