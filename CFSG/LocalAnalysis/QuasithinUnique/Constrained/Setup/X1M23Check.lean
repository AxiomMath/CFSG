module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PermCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M23Data
public import CFSG.Sporadic.Schreier.M23Gens
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PermCheck
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M23Data
public meta import CFSG.Sporadic.Schreier.M23Gens
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M23CheckInputs
public import Certificates.Certificate4037
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

open CFSG.Sporadic.Schreier CFSG.Blueprint

theorem m23_sylow_check :
    m23rl.length = 2 ^ 7 ∧ m23rl.Nodup ∧ (1 : ↥NativeSporadic.M23) ∈ m23rl ∧
      (∀ x ∈ m23rl, ∀ y ∈ m23rl, x * y ∈ m23rl) ∧ (∀ x ∈ m23rl, x ^ (2 ^ 7) = 1) :=
  Certificates.certificate4037.1

theorem m23_rank_check :
    forallIndep m23rinv (fun _ => false) 5 [] = true :=
  Certificates.certificate4037.2.1

theorem m23_G1_check : m23G1ok = true ∧ m23G1cover = true :=
  Certificates.certificate4037.2.2.1

theorem m23_G2_check : m23G2ok = true ∧ m23G2cover = true :=
  Certificates.certificate4037.2.2.2

end CFSG.QuasithinUnique.Setup.X1
