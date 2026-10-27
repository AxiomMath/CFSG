module

public import CFSG.LocalAnalysis.ComponentClassification.GSLitMaximalTriple
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWeakCorr

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {X : Type} [Group X] [Finite X]

theorem isoCorr_of_commuting_involution_of_bound [IsSimpleGroup X]
    (hS : SchreierFor Blueprint.Catalog) (hnonab : ∃ u v : X, u * v ≠ v * u)
    (hK : Assembly.KProper Blueprint.Catalog X) {a x : X} {J : Subgroup X}
    (hmax : GSMaximalUnbalancingTriple a x J)
    (hbound : ∀ (u v : X) (K : Subgroup X), GSUnbalancingTriple u v K → GrSLit.GSWeakReach J K →
      (pPrimeCore 2 K).index ≤ (pPrimeCore 2 J).index)
    {y b : X} (hy : y ∈ centralizer ({a} : Set X) ⊓ normalizer (J : Set X))
    (hUy : GSUnbalancingTriple a y J) (hb : orderOf b = 2) (hab : a * b = b * a)
    (hyb : y * b = b * y) (hbJ : b ∈ coreActionKernel J) :
    ∃ M : Subgroup X, UnbalancedGS.GSIsoCorr a J b M ∧ GSUnbalancingTriple b y M := by
  obtain ⟨hbN, hbcomm⟩ := mem_coreActionKernel.mp hbJ
  have hbZ : b ∉ center X := GSLit.not_mem_center_of_orderOf_eq_two hnonab hb
  obtain ⟨M, hW, hUM, hidx, hcorr⟩ :=
    GrSLit.exists_gsWeakCorr_of_target hS hK hUy hb hbZ hab hyb hbN hbcomm
  have heq : (pPrimeCore 2 J).index = (pPrimeCore 2 M).index :=
    le_antisymm hidx (hbound b y M hUM (GrSLit.GSWeakReach.single hW))
  have hC : UnbalancedGS.GSCorr a J b M := hcorr (Or.inr heq)
  exact ⟨M, (hmax.2 b M hb (mem_centralizer_singleton_iff.mpr hab.symm) hC).1 y hy hUM, hUM⟩

end CFSG.ComponentClassification.GSThmB
