module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PermCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1MathieuGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PairCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1OuterGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24Data
public import CFSG.Sporadic.Schreier.M24
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PermCheck
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1MathieuGen
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PairCover
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24Data
public meta import CFSG.Sporadic.Schreier.M24
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24CheckInputs
public import Certificates.Certificate4059
public meta import CFSG.Foundations
public meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public meta import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint

theorem m24_sylow_check :
    m24rl.length = 2 ^ 10 ∧ m24rl.Nodup ∧ (1 : ↥NativeSporadic.M24) ∈ m24rl ∧
      (∀ x ∈ m24rl, ∀ g ∈ m24rg, x * g ∈ m24rl) ∧ (∀ x ∈ m24rl, x ^ (2 ^ 10) = 1) :=
  Certificates.certificate4059.1

theorem m24_count_check :
    (pairG (invG m24rl)).length < (2 ^ (6 + 1) - 1) * (2 ^ (6 + 1) - 2) :=
  Certificates.certificate4059.2.1

theorem m24_G1_check :
    g1ok m24rl m24conj m24G1 11 = true ∧ g1cover m24rl m24G1 = true :=
  Certificates.certificate4059.2.2.1

theorem m24_G2_11_check :
    g2ok m24rl m24conj m24G2_11 11 = true ∧ (g2coverBad m24key m24rl m24G2_11).length = 0 :=
  Certificates.certificate4059.2.2.2.1

theorem m24_G2_23_check :
    g2ok m24rl m24conj m24G2_23 23 = true ∧
      (g2coverBad m24key m24rl m24G2_23).length < 930 :=
  Certificates.certificate4059.2.2.2.2

end CFSG.QuasithinUnique.Setup.X1
