module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PermCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1MathieuGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22Data
public import CFSG.Sporadic.Schreier.M22
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PermCheck
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1MathieuGen
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22Data
public meta import CFSG.Sporadic.Schreier.M22
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22CheckInputs
public import Certificates.Certificate4057
public meta import CFSG.Foundations
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public meta import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint

theorem m22_sylow_check :
    m22rl.length = 2 ^ 7 ∧ m22rl.Nodup ∧ (1 : ↥NativeSporadic.M22) ∈ m22rl ∧
      (∀ x ∈ m22rl, ∀ y ∈ m22rl, x * y ∈ m22rl) ∧ (∀ x ∈ m22rl, x ^ (2 ^ 7) = 1) :=
  Certificates.certificate4057.1

theorem m22_rank_check :
    forallIndep (invG m22rl) (fun _ => false) 5 [] = true :=
  Certificates.certificate4057.2.1

theorem m22_G1_check :
    g1ok m22rl m22conj m22G1 11 = true ∧ g1cover m22rl m22G1 = true :=
  Certificates.certificate4057.2.2.1

theorem m22_G2_check :
    g2ok m22rl m22conj m22G2 11 = true ∧ g2cover m22rl m22G2 = true :=
  Certificates.certificate4057.2.2.2

end CFSG.QuasithinUnique.Setup.X1
