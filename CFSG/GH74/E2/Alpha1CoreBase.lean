
module

public import CFSG.GH74.E2.Alpha1Rank
public import CFSG.GH74.E2.Cl2Quot
public import CFSG.GH74.E2.DirectProd
public import CFSG.GH74.E2.Tools
public import CFSG.GH74.E2.DirectSylow
public import CFSG.GH74.E2.Alpha1AutCert
public import CFSG.GH74.GLS.Types
public import CFSG.Open.Catalog
public import CFSG.GH74.E2.NonCentralProd
public import CFSG.GH74.E2.QuasiRank
public import CFSG.GH74.E2.FrattiniRank
public import CFSG.GH74.E2.CaseIGlue
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupCommuting
public meta import Mathlib
public meta import CFSG.CharacterTheory.Semidihedral.Model
public meta import CFSG.GH74.E2.SD16Cert
public import CFSG.GH74.E2.Alpha1CoreInputs
public meta import CFSG.GH74.E2.Alpha1CoreInputs
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.GH74.AS16.Defs
public import CFSG.GH74.E2.Components
public import CFSG.GH74.E2.DtSylow
public import CFSG.GH74.E2.OddRankG
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import Certificates.Certificate3953
public import Certificates.Certificate5007
public import Certificates.Certificate5022
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

@[expose] public section

namespace CFSG.GH74.E2

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.Semidihedral

section SD16Facts

instance (x : SD16M) : Decidable (IsCentralInv16 x) :=
  inferInstanceAs (Decidable ((∀ w, w * x = x * w) ∧ x * x = 1))

end SD16Facts

end CFSG.GH74.E2
