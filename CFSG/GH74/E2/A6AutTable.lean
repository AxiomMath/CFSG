module

public import Mathlib
public import CFSG.GH74.E2.Q8C2Check
public import CFSG.GH74.E2.A6Sylow
public import CFSG.GH74.KGroups.A6
public meta import Mathlib
public meta import CFSG.GH74.E2.Q8C2Check
public meta import CFSG.GH74.KGroups.A6
public import Certificates.Certificate5003
public import Certificates.Certificate5108
public import CFSG.Foundations
public import CFSG.GH74.SectionalRank
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases

public section

namespace CFSG.GH74.E2

open CFSG.GH74.KGroups

theorem a6_q8c2_ok :
    q8c2free (elemsT A6.QA) = true :=
  Certificates.certificate5003

theorem noQ8C2_A6
    {K : Type} [Group K] (hK : ShapeA6 K) : NoQ8C2 (MulAut K) := by
  obtain ⟨e⟩ := A6.equiv_of_alt6 (shapeA6_alternating hK)
  obtain ⟨M, -, hA⟩ := A6.autModel e
  exact noQ8C2_mulAut_of_check M A6.QA A6.QA_ok hA a6_q8c2_ok

end CFSG.GH74.E2
