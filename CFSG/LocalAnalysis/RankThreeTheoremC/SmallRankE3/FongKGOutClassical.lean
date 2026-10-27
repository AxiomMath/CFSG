module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGOutGen
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongOut

open CFSG.RankThree.PartOne.OutStructure CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof
  CFSG.Assembly.LowTwoRank

theorem outTwoCyclic_PSL_two {X : Type} [Group X] {m : ℕ}
    (h : StatedClassicalModel X .PSL 2 2 m) : OutTwoCyclic X := by
  have : Finite X := by
    obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h
    exact Finite.of_equiv _ e.symm.toEquiv
  exact outTwoCyclic_of_outPNice_two (outPNice_PSL_two Nat.prime_two h)

theorem outTwoCyclic_PSp {X : Type} [Group X] {r m : ℕ} (hr : 2 ≤ r)
    (h : StatedClassicalModel X .PSp r 2 m) : OutTwoCyclic X := by
  have : Finite X := by
    obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h
    exact Finite.of_equiv _ e.symm.toEquiv
  rcases Nat.lt_or_ge r 3 with hr3 | hr3
  · obtain rfl : r = 2 := by omega
    exact outTwoCyclic_of_outPNice_two (outPNice_PSp_two Nat.prime_two h)
  · exact outTwoCyclic_of_outPNice_two (outPNice_PSp_ge_three Nat.prime_two hr3 h)

theorem outTwoCyclic_PSU {X : Type} [Group X] {n m : ℕ}
    (h : StatedClassicalModel X .PSU n 2 m) : OutTwoCyclic X := by
  have hm : 1 ≤ m := h.1.2.1
  have : Finite X := by
    obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h
    exact Finite.of_equiv _ e.symm.toEquiv
  refine outTwoCyclic_of_outPNice_two (outPNice_PSU Nat.prime_two h ?_)
  intro hd
  have h1 : 2 ∣ 2 ^ m + 1 := hd.trans (Nat.gcd_dvd_right _ _)
  have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  omega

theorem outTwoCyclic_PSL_odd {X : Type} [Group X] {n m : ℕ} (hn : 3 ≤ n) (hm : Odd m)
    (h : StatedClassicalModel X .PSL n 2 m) : OutTwoCyclic X := by
  have hm1 : 1 ≤ m := h.1.2.1
  have hdvd : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) ∣
      2 * m * Nat.gcd n (2 ^ m - 1) :=
    (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound X n 2 m h).2.2.2.2 hn
  have : Finite X := by
    obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h
    exact Finite.of_equiv _ e.symm.toEquiv
  have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have hpos : 0 < 2 ^ m := by positivity
  have hodd : Odd (2 ^ m - 1) := by
    obtain ⟨c, hc⟩ := h2
    exact ⟨c - 1, by omega⟩
  have hgodd : Odd (Nat.gcd n (2 ^ m - 1)) := Odd.of_dvd_nat hodd (Nat.gcd_dvd_right _ _)
  obtain ⟨k, hk⟩ := hm.mul hgodd
  apply outTwoCyclic_of_not_four_dvd_card_outer
  intro h4
  have h4' := h4.trans hdvd
  have e2 : 2 * m * Nat.gcd n (2 ^ m - 1) = 2 * (2 * k + 1) := by
    rw [← hk, mul_assoc]
  rw [e2] at h4'
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongOut
