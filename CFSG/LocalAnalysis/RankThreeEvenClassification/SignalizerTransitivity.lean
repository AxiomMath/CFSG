module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerIntersectionGrowth

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem signalizer_prime_compatible_transitivity
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroupPrime : ℕ) (hsubgroupPrime : subgroupPrime.Prime)
    (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (hcomm : IsMulCommutative actor) (hpower : ∀ member : actor, member ^ prime = 1)
    (hcard : Nat.card actor = prime ^ 3) (initialFirst initialSecond : Subgroup G)
    (hinitialFirst : Maximal (SignalizerPrimeCompatible prime subgroupPrime actor signalizer) initialFirst)
    (hinitialSecond : Maximal (SignalizerPrimeCompatible prime subgroupPrime actor signalizer) initialSecond) :
    CommonFixedConjugate actor signalizer initialFirst initialSecond := by
  classical
  by_contra hinitial
  let badPairs := {pair : Subgroup G × Subgroup G //
    Maximal (SignalizerPrimeCompatible prime subgroupPrime actor signalizer) pair.1 ∧
    Maximal (SignalizerPrimeCompatible prime subgroupPrime actor signalizer) pair.2 ∧
    ¬CommonFixedConjugate actor signalizer pair.1 pair.2}
  have : Nonempty badPairs := ⟨⟨(initialFirst, initialSecond), hinitialFirst, hinitialSecond, hinitial⟩⟩
  obtain ⟨largestPair, hsizeMaximal⟩ := Finite.exists_max
    (fun pair : badPairs => Nat.card (pair.1.1 ⊓ pair.1.2 : Subgroup G))
  let first := largestPair.1.1
  let second := largestPair.1.2
  let lower := first ⊓ second
  have hfirst : Maximal (SignalizerPrimeCompatible prime subgroupPrime actor signalizer) first :=
    largestPair.2.1
  have hsecond : Maximal (SignalizerPrimeCompatible prime subgroupPrime actor signalizer) second :=
    largestPair.2.2.1
  have hnotConjugate : ¬CommonFixedConjugate actor signalizer first second := largestPair.2.2.2
  have hfirstStrict : first ⊓ second < first := by
    apply lt_of_le_of_ne inf_le_left
    intro heq
    have hle : first ≤ second := by
      rw [← heq]
      exact inf_le_right
    have hequal := hfirst.eq_of_le hsecond.1 hle
    apply hnotConjugate
    rw [hequal]
    exact CommonFixedConjugate.refl actor signalizer second
  have hsecondStrict : first ⊓ second < second := by
    apply lt_of_le_of_ne inf_le_right
    intro heq
    have hle : second ≤ first := by
      rw [← heq]
      exact inf_le_left
    have hequal := hsecond.eq_of_le hfirst.1 hle
    apply hnotConjugate
    rw [hequal]
    exact CommonFixedConjugate.refl actor signalizer first
  have hlargerConjugate : ∀ left right : Subgroup G,
      Maximal (SignalizerPrimeCompatible prime subgroupPrime actor signalizer) left →
      Maximal (SignalizerPrimeCompatible prime subgroupPrime actor signalizer) right →
      Nat.card lower < Nat.card (left ⊓ right : Subgroup G) →
        CommonFixedConjugate actor signalizer left right := by
    intro left right hleft hright hlarger
    by_contra hnot
    have hbounded := hsizeMaximal ⟨(left, right), hleft, hright, hnot⟩
    change Nat.card (left ⊓ right : Subgroup G) ≤ Nat.card lower at hbounded
    omega
  obtain ⟨conjugator, hconjugator, maximal, hmaximal, hfirstGrowth, hsecondGrowth⟩ :=
    signalizer_prime_compatible_intersection_growth prime hprime subgroupPrime hsubgroupPrime
      actor signalizer hsignalizer hcomm hpower hcard first second hfirst.1 hsecond.1
        hfirstStrict hsecondStrict
  have hfirstConjugateMaximal := maximal_signalizer_prime_compatible_conjugate prime subgroupPrime
    actor signalizer hsignalizer first hfirst conjugator hconjugator
  have hfirstMaximalConjugate := hlargerConjugate _ _ hfirstConjugateMaximal hmaximal
    (subgroup_card_lt_of_lt _ _ hfirstGrowth)
  have hsecondMaximalConjugate := hlargerConjugate _ _ hsecond hmaximal
    (subgroup_card_lt_of_lt _ _ hsecondGrowth)
  have hfirstOwnConjugate : CommonFixedConjugate actor signalizer first
      (first.map (MulAut.conj conjugator).toMonoidHom) := ⟨conjugator, hconjugator, rfl⟩
  apply hnotConjugate
  exact CommonFixedConjugate.trans actor signalizer first maximal second
    (CommonFixedConjugate.trans actor signalizer first _ maximal hfirstOwnConjugate hfirstMaximalConjugate)
    (CommonFixedConjugate.symm actor signalizer second maximal hsecondMaximalConjugate)

end CFSG.RankThreeEvenClassification.Helpers
