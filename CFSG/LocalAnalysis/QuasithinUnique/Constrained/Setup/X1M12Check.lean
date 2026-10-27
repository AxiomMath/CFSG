module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PermCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1MathieuGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M12Data
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Outer
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PermCheck
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1MathieuGen
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M12Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM12ModelData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M12CheckInputs
public import Certificates.Certificate4069
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

theorem m12_sylow_check :
    m12rl.length = 2 ^ 6 ∧ m12rl.Nodup ∧ (1 : ↥NativeSporadic.M12) ∈ m12rl ∧
      (∀ x ∈ m12rl, ∀ y ∈ m12rl, x * y ∈ m12rl) ∧ (∀ x ∈ m12rl, x ^ (2 ^ 6) = 1) :=
  Certificates.certificate4069.1

theorem m12_rank_check :
    forallIndep (invG m12rl) (fun _ => false) 4 [] = true :=
  Certificates.certificate4069.2.1

theorem m12_G1_check :
    g1ok m12rl m12conj m12G1 11 = true ∧ g1cover m12rl m12G1 = true :=
  Certificates.certificate4069.2.2.1

theorem m12_outer_check :
    (m12Sigma * (evalCodes [m12A1, m12B1] m12OuterWord * m12Sigma *
        (evalCodes [m12A1, m12B1] m12OuterWord)⁻¹)) ^ 11 = 1 ∧
      m12Sigma * (evalCodes [m12A1, m12B1] m12OuterWord * m12Sigma *
        (evalCodes [m12A1, m12B1] m12OuterWord)⁻¹) ≠ 1 :=
  Certificates.certificate4069.2.2.2

end CFSG.QuasithinUnique.Setup.X1
