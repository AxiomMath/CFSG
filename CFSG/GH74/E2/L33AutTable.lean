module

public import Mathlib
public import CFSG.GH74.E2.Q8C2Check
public import CFSG.GH74.E2.Shapes
public import CFSG.GH74.KGroups.L33
public meta import Mathlib
public meta import CFSG.GH74.E2.Q8C2Check
public meta import CFSG.GH74.KGroups.L33
public import Certificates.Certificate5011
public import Certificates.Certificate5120
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

public section

namespace CFSG.GH74.E2

open CFSG.GH74.KGroups

theorem l33_q8c2_ok :
    q8c2free (elemsT L33.QA) = true :=
  Certificates.certificate5011

theorem noQ8C2_L33
    {K : Type} [Group K] (hK : ShapeL33 K) : NoQ8C2 (MulAut K) := by
  obtain ⟨e⟩ := L33.equiv_of_lieModel hK
  obtain ⟨M, -, hA⟩ := L33.autModel e
  exact noQ8C2_mulAut_of_check M L33.QA L33.QA_ok hA l33_q8c2_ok

end CFSG.GH74.E2
