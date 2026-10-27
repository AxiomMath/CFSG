module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangG2Odd
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangG2Even
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerOne
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerFamG2
public import CFSG.LieType.SeitzGeneration.ExcCatModels
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.RankThree.PartOne.K133H.G2Plane

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.TauCetiBridge CFSG.RankThree.PartOne.SEITZ3

set_option linter.unusedSectionVars false

theorem dvd_add_one_of_orderOf_eq_two {p n : ℕ} (hp : p.Prime)
    (h : orderOf ((n : ℕ) : ZMod p) = 2) : p ∣ n + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : ((n : ℕ) : ZMod p) ^ 2 = 1 := by
    rw [← h]
    exact pow_orderOf_eq_one _
  have h2 : ((n : ℕ) : ZMod p) ≠ 1 := fun h' => by
    rw [h', orderOf_one] at h
    omega
  have h3 : (((n : ℕ) : ZMod p) - 1) * (((n : ℕ) : ZMod p) + 1) = 0 := by
    linear_combination h1
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact absurd (sub_eq_zero.1 h4) h2
  · rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    exact h4

section Classes

theorem innerPlaneBalanceAt_G2_two (hmax : MaxSL2SL2G2) : InnerPlaneBalanceAt .G2 2 := by
  intro q hv p hp hp7 _ hpq he
  obtain ⟨K, _, _, hK, hKc, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
  have hdvd : p ∣ Nat.card K + 1 := by
    rw [hK]
    exact dvd_add_one_of_orderOf_eq_two hp he
  have := (finite_isSimpleGroup_cat_G2 hv).2
  have hsimple : IsSimpleGroup (adjointGroup Tag.G2 K) := MulEquiv.isSimpleGroup e.symm
  by_cases h2 : q.p = 2
  · have : CharP K 2 := by
      rw [h2] at hKc
      exact hKc
    exact InnerPlaneBalance.of_mulEquiv e
      (innerPlaneBalance_adjointG2_qplus_even hmax K hp (by omega) hdvd)
  · have hodd : Odd (Nat.card K) := by
      rw [hK, TauCeti.PrimePower.card_def]
      exact (q.prime_p.odd_of_ne_two h2).pow
    exact InnerPlaneBalance.of_mulEquiv e
      (innerPlaneBalance_adjointG2_qplus_odd K hodd hp (by omega) hdvd)

end Classes

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
