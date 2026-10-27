module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.MW3Co1Center
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Sporadic.Co1.Module.OddCent

public section

namespace CFSG.EvenSporadicStandard.TwoB.MW3

open CFSG.Blueprint CFSG.Monster CFSG.Monster.GMS CFSG.Monster.B.TwoA.Census
  CFSG.Monster.Existence CFSG.Sporadic.Co1.Module.Odd

theorem isConj_rho3_of_fix
    {r : NativeSporadic.Co1} (hr : orderOf r = 2)
    (hf : (co1Fix r).ncard = 2 ^ 16) : IsConj rho3 r := by
  obtain ⟨-, -, hmem, hcls, -⟩ := lattice_quotient_three_involution_classes
  obtain ⟨c, hc⟩ := CFSG.Sporadic.Co1.Module.exists_conj_three_of_chevalley monoN hmem hcls
  obtain ⟨sA, sB, sC, hrep⟩ := CFSG.Sporadic.Co1.Module.rep_facts
  have hcl := co1Inv_classes hrep c hc
  obtain ⟨hoA, hoB, hoC, hfA, hfB, hfC, -⟩ := hrep
  have hA : ∀ s : NativeSporadic.Co1, orderOf s = 2 → (co1Fix s).ncard = 2 ^ 16 →
      IsConj s sA := by
    intro s hs hfs
    rcases hcl s hs with h | h | h
    · exact h
    · have := (co1Inv_isConj_invariants h).1
      rw [hfs] at this
      have e : (co1Fix sB).ncard = 2 ^ 12 := hfB
      rw [e] at this
      norm_num at this
    · have := (co1Inv_isConj_invariants h).1
      rw [hfs] at this
      have e : (co1Fix sC).ncard = 2 ^ 12 := hfC
      rw [e] at this
      norm_num at this
  exact ((hA _ orderOf_rho3 rho3_ncard_fix).trans (hA r hr hf).symm)

theorem eq_one_or_eq_of_commute_of_fix
    {r ζ : NativeSporadic.Co1}
    (hr : orderOf r = 2) (hf : (co1Fix r).ncard = 2 ^ 16)
    (hζ : ∀ d ∈ Subgroup.centralizer ({r} : Set NativeSporadic.Co1), ζ * d = d * ζ) :
    ζ = 1 ∨ ζ = r :=
  eq_one_or_eq_of_commute_of_isConj (isConj_rho3_of_fix hr hf) hζ

end CFSG.EvenSporadicStandard.TwoB.MW3
