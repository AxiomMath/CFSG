module

public import CFSG.HardMathSupport.Solomon.Coordinator.I713
public import CFSG.HardMathSupport.Solomon.Coordinator.I713OuterDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms

theorem card_inner_dvd (K : Type) [Group K] [Finite K] :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner K) ∣ Nat.card K := by
  unfold CFSG.ComponentClassification.OuterAutomorphisms.inner
  exact Subgroup.card_range_dvd _

theorem pRank_outer_eq_of_not_dvd {p : ℕ} (hp : p.Prime) (K : Type) [Group K] [Finite K]
    (hpK : ¬ p ∣ Nat.card K) :
    CFSG.Open.pRank p (⊤ : Subgroup (Outer K)) = CFSG.Open.pRank p (⊤ : Subgroup (MulAut K)) := by
  have : Fact p.Prime := ⟨hp⟩
  exact CFSG.SectionRank.pRank_quotient_eq (CFSG.ComponentClassification.OuterAutomorphisms.inner K)
    fun h => hpK (h.trans (card_inner_dvd K))

theorem i_7_13_1_outerPPrime_of_pPrime (h : I_7_13_1_pPrime) : I_7_13_1_OuterPPrime := by
  intro p hp hp2 K _ _ hs hn hcat hpK
  rw [pRank_outer_eq_of_not_dvd hp K hpK]
  exact h p hp hp2 K hs hn hcat hpK

theorem i_7_13_1_outerPPrime_holds :
    I_7_13_1_OuterPPrime :=
  i_7_13_1_outerPPrime_of_pPrime i_7_13_1_pPrime_holds

end CFSG.HardMathSupport.Solomon.Coordinator
