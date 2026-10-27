module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.TitsCoverCheck
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.TitsCoverCheck
public import Certificates.Certificate4104
public meta import CFSG.Assembly.OrderReductions.InvertedSubgroup
public meta import CFSG.Assembly.OrderReductions.OddInversion
public meta import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public meta import CFSG.LieType.Chevalley.RootCommutator
public meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public meta import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public meta import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public meta import CFSG.Sporadic.Schreier.TitsOther
public meta import CFSG.Sporadic.Schreier.TitsOuter
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic

public section

namespace CFSG.QuasithinUnique.Ch1.TitsCover

theorem covCheck_covData : covCheck covData = true :=
  Certificates.certificate4104.1

theorem covData_nV : covData.nV = 2048 :=
  Certificates.certificate4104.2

end CFSG.QuasithinUnique.Ch1.TitsCover
