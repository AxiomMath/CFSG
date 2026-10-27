module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.ECoreClasses
public import CFSG.Sporadic.Co1.Module.OddCent

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Sporadic.Co1.Cover CFSG.Blueprint CFSG.Monster.GMS

theorem isConj_of_ncard_fix_eq
    {s t : NativeSporadic.Co1} (hs : orderOf s = 2) (ht : orderOf t = 2)
    (hfs : (co1Fix s).ncard = 2 ^ 16) (hft : (co1Fix t).ncard = 2 ^ 16) : IsConj s t := by
  obtain ⟨sA, sB, sC, hrep, hcls⟩ := co1_involution_classes
  obtain ⟨-, -, -, hfA, hfB, hfC, -, -, -, -⟩ := hrep
  have key : ∀ u : NativeSporadic.Co1, orderOf u = 2 → (co1Fix u).ncard = 2 ^ 16 →
      IsConj u sA := by
    intro u hu hfu
    rcases hcls u hu with h | h | h
    · exact h
    · exfalso
      have h1 := (co1Inv_isConj_invariants h).1
      have e2 : (co1Fix sB).ncard = 2 ^ 12 := hfB
      rw [hfu, e2] at h1
      norm_num at h1
    · exfalso
      have h1 := (co1Inv_isConj_invariants h).1
      have e2 : (co1Fix sC).ncard = 2 ^ 12 := hfC
      rw [hfu, e2] at h1
      norm_num at h1
  exact (key s hs hfs).trans (key t ht hft).symm

theorem isCo1TwoA_epsA :
    IsCo1TwoA (epsMask eMaskA) := by
  obtain ⟨hoA, hfixA⟩ := epsA_facts
  have hfix : (co1Fix (epsMask eMaskA)).ncard = 2 ^ 16 := hfixA
  have hconj : IsConj (epsMask eMaskA) CFSG.Sporadic.Co1.Module.Odd.rho3 :=
    isConj_of_ncard_fix_eq hoA CFSG.Sporadic.Co1.Module.Odd.orderOf_rho3 hfix
      CFSG.Sporadic.Co1.Module.Odd.rho3_ncard_fix
  obtain ⟨c1, -, c3⟩ := co1Inv_isConj_invariants hconj
  refine ⟨hoA, ?_⟩
  rw [c1, c3]
  exact CFSG.Sporadic.Co1.Module.Odd.isCo1TwoA_rho3.2

end CFSG.EvenSporadicStandard.TwoCo1
