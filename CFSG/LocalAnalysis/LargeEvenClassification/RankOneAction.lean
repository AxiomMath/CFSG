module

public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut

public section

open CFSG.Open
open scoped MatrixGroups

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem binary_GL_three_card_dvd {dimension : ℕ} (hdimension : dimension ≤ 3) :
    Nat.card (GL (Fin dimension) (ZMod 2)) ∣ 168 := by
  rw [Matrix.card_GL_field]
  interval_cases dimension <;> norm_num [Fin.prod_univ_succ]

theorem two_group_three_generator_aut_prime_support {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (hrank : pGeneratorRank 2 Ambient ≤ 3)
    {prime : ℕ} (hprime : prime.Prime) (hdivides : prime ∣ Nat.card (MulAut Ambient)) :
    prime = 2 ∨ prime = 3 ∨ prime = 7 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CommGroup (Ambient ⧸ frattini Ambient) := pGroupFrattiniCommGroup Nat.prime_two hpgroup
  let module : Module (ZMod 2) (Additive (Ambient ⧸ frattini Ambient)) :=
    elementaryZModModule (pGroup_frattini_quotient_exponent Nat.prime_two hpgroup)
  let linearAction := (elementaryAutLinear 2).comp (frattiniAutAction Ambient)
  have hlinearKernel : linearAction.ker = (frattiniAutAction Ambient).ker := by
    ext automorphism
    change elementaryAutLinear 2 (frattiniAutAction Ambient automorphism) = 1 ↔
      frattiniAutAction Ambient automorphism = 1
    constructor
    · intro heq
      apply elementaryAutLinear_injective 2
      exact heq.trans (map_one (elementaryAutLinear 2)).symm
    · intro heq
      rw [heq, map_one]
  have hkernelGroup : IsPGroup 2 linearAction.ker := by
    rw [hlinearKernel]
    exact frattiniAutAction_isPGroup_ker Ambient Nat.prime_two hpgroup
  obtain ⟨kernelRank, hkernelCard⟩ := hkernelGroup.exists_card_eq
  have hdimension : Module.finrank (ZMod 2) (Additive (Ambient ⧸ frattini Ambient)) ≤ 3 := by
    rw [← pGeneratorRank_eq_frattini_finrank Nat.prime_two hpgroup module]
    exact hrank
  have hrangeDivides : Nat.card linearAction.range ∣ 168 := by
    have hcard := linearAction.range.card_subgroup_dvd_card
    rw [card_linear_aut_binary] at hcard
    exact hcard.trans (binary_GL_three_card_dvd hdimension)
  have hformula := Subgroup.card_eq_card_quotient_mul_card_subgroup linearAction.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange linearAction).toEquiv, hkernelCard] at hformula
  rw [hformula] at hdivides
  rcases hprime.dvd_mul.mp hdivides with himage | hkernel
  · have hsmallDivides : prime ∣ 168 := himage.trans hrangeDivides
    have hfactorization : 168 = 2 ^ 3 * 3 * 7 := by norm_num
    rw [hfactorization] at hsmallDivides
    rcases hprime.dvd_mul.mp hsmallDivides with hfirst | hseven
    · rcases hprime.dvd_mul.mp hfirst with htwo | hthree
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp (hprime.dvd_of_dvd_pow htwo))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hprime (by norm_num)).mp hthree))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hprime (by norm_num)).mp hseven))
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp (hprime.dvd_of_dvd_pow hkernel))

theorem rank_one_two_group_aut_prime_support {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (hrank : twoRank Ambient ≤ 1)
    {prime : ℕ} (hprime : prime.Prime) (hdivides : prime ∣ Nat.card (MulAut Ambient)) :
    prime = 2 ∨ prime = 3 ∨ prime = 7 :=
  two_group_three_generator_aut_prime_support hpgroup
    (rank_one_two_group_generator_rank_le_three hpgroup hrank) hprime hdivides

theorem nontrivial_pGroup_action_prime_divides {Acting Ambient : Type groupUniverse} [Group Acting]
    [Group Ambient] [Finite Acting] [Finite Ambient] {prime : ℕ} (hprime : prime.Prime)
    (hpacting : IsPGroup prime Acting) (action : Acting →* MulAut Ambient) (hnontrivial : action.range ≠ ⊥) :
    prime ∣ Nat.card (MulAut Ambient) := by
  let : Fact prime.Prime := ⟨hprime⟩
  have himageGroup : IsPGroup prime action.range :=
    hpacting.of_surjective action.rangeRestrict action.rangeRestrict_surjective
  obtain ⟨imageRank, hcard⟩ := himageGroup.exists_card_eq
  have hpositive : imageRank ≠ 0 := by
    intro hzero
    apply hnontrivial
    apply Subgroup.card_eq_one.mp
    rw [hcard, hzero, pow_zero]
  exact (hcard.symm ▸ dvd_pow_self prime hpositive).trans action.range.card_subgroup_dvd_card

theorem nontrivial_odd_action_two_rank_two {Acting Ambient : Type groupUniverse} [Group Acting]
    [Group Ambient] [Finite Acting] [Finite Ambient] {prime : ℕ} (hprime : prime.Prime)
    (hlarge : 3 < prime) (hnotSeven : prime ≠ 7) (hpacting : IsPGroup prime Acting)
    (hpgroup : IsPGroup 2 Ambient) (action : Acting →* MulAut Ambient) (hnontrivial : action.range ≠ ⊥) :
    2 ≤ twoRank Ambient := by
  by_contra hnotRank
  have hsmall : twoRank Ambient ≤ 1 := by omega
  have hoptions := rank_one_two_group_aut_prime_support hpgroup hsmall hprime
    (nontrivial_pGroup_action_prime_divides hprime hpacting action hnontrivial)
  rcases hoptions with htwo | hthree | hseven
  · omega
  · omega
  · exact hnotSeven hseven

theorem binary_GL_two_card_dvd {dimension : ℕ} (hdimension : dimension ≤ 2) :
    Nat.card (GL (Fin dimension) (ZMod 2)) ∣ 6 := by
  rw [Matrix.card_GL_field]
  interval_cases dimension <;> norm_num [Fin.prod_univ_succ]

theorem two_group_two_generator_aut_prime_support {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (hrank : pGeneratorRank 2 Ambient ≤ 2)
    {prime : ℕ} (hprime : prime.Prime) (hdivides : prime ∣ Nat.card (MulAut Ambient)) :
    prime = 2 ∨ prime = 3 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CommGroup (Ambient ⧸ frattini Ambient) := pGroupFrattiniCommGroup Nat.prime_two hpgroup
  let module : Module (ZMod 2) (Additive (Ambient ⧸ frattini Ambient)) :=
    elementaryZModModule (pGroup_frattini_quotient_exponent Nat.prime_two hpgroup)
  let linearAction := (elementaryAutLinear 2).comp (frattiniAutAction Ambient)
  have hlinearKernel : linearAction.ker = (frattiniAutAction Ambient).ker := by
    ext automorphism
    change elementaryAutLinear 2 (frattiniAutAction Ambient automorphism) = 1 ↔
      frattiniAutAction Ambient automorphism = 1
    constructor
    · intro heq
      apply elementaryAutLinear_injective 2
      exact heq.trans (map_one (elementaryAutLinear 2)).symm
    · intro heq
      rw [heq, map_one]
  have hkernelGroup : IsPGroup 2 linearAction.ker := by
    rw [hlinearKernel]
    exact frattiniAutAction_isPGroup_ker Ambient Nat.prime_two hpgroup
  obtain ⟨kernelRank, hkernelCard⟩ := hkernelGroup.exists_card_eq
  have hdimension : Module.finrank (ZMod 2) (Additive (Ambient ⧸ frattini Ambient)) ≤ 2 := by
    rw [← pGeneratorRank_eq_frattini_finrank Nat.prime_two hpgroup module]
    exact hrank
  have hrangeDivides : Nat.card linearAction.range ∣ 6 := by
    have hcard := linearAction.range.card_subgroup_dvd_card
    rw [card_linear_aut_binary] at hcard
    exact hcard.trans (binary_GL_two_card_dvd hdimension)
  have hformula := Subgroup.card_eq_card_quotient_mul_card_subgroup linearAction.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange linearAction).toEquiv, hkernelCard] at hformula
  rw [hformula] at hdivides
  rcases hprime.dvd_mul.mp hdivides with himage | hkernel
  · have hsmallDivides : prime ∣ 6 := himage.trans hrangeDivides
    have hfactorization : 6 = 2 * 3 := by norm_num
    rw [hfactorization] at hsmallDivides
    rcases hprime.dvd_mul.mp hsmallDivides with htwo | hthree
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp htwo)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hprime (by norm_num)).mp hthree)
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp (hprime.dvd_of_dvd_pow hkernel))

theorem rank_one_two_group_aut_prime_support_exact {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (hrank : twoRank Ambient ≤ 1)
    {prime : ℕ} (hprime : prime.Prime) (hdivides : prime ∣ Nat.card (MulAut Ambient)) :
    prime = 2 ∨ prime = 3 :=
  two_group_two_generator_aut_prime_support hpgroup
    (rank_one_two_group_generator_rank_le_two hpgroup hrank) hprime hdivides

theorem two_group_two_generator_aut_card_dvd {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (hrank : pGeneratorRank 2 Ambient ≤ 2) :
    ∃ exponent : ℕ, Nat.card (MulAut Ambient) ∣ 6 * 2 ^ exponent := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CommGroup (Ambient ⧸ frattini Ambient) := pGroupFrattiniCommGroup Nat.prime_two hpgroup
  let module : Module (ZMod 2) (Additive (Ambient ⧸ frattini Ambient)) :=
    elementaryZModModule (pGroup_frattini_quotient_exponent Nat.prime_two hpgroup)
  let linearAction := (elementaryAutLinear 2).comp (frattiniAutAction Ambient)
  have hlinearKernel : linearAction.ker = (frattiniAutAction Ambient).ker := by
    ext automorphism
    change elementaryAutLinear 2 (frattiniAutAction Ambient automorphism) = 1 ↔
      frattiniAutAction Ambient automorphism = 1
    constructor
    · intro heq
      apply elementaryAutLinear_injective 2
      exact heq.trans (map_one (elementaryAutLinear 2)).symm
    · intro heq
      rw [heq, map_one]
  have hkernelGroup : IsPGroup 2 linearAction.ker := by
    rw [hlinearKernel]
    exact frattiniAutAction_isPGroup_ker Ambient Nat.prime_two hpgroup
  obtain ⟨exponent, hkernelCard⟩ := hkernelGroup.exists_card_eq
  have hdimension : Module.finrank (ZMod 2) (Additive (Ambient ⧸ frattini Ambient)) ≤ 2 := by
    rw [← pGeneratorRank_eq_frattini_finrank Nat.prime_two hpgroup module]
    exact hrank
  have hrangeDivides : Nat.card linearAction.range ∣ 6 := by
    have hcard := linearAction.range.card_subgroup_dvd_card
    rw [card_linear_aut_binary] at hcard
    exact hcard.trans (binary_GL_two_card_dvd hdimension)
  have hformula := Subgroup.card_eq_card_quotient_mul_card_subgroup linearAction.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange linearAction).toEquiv, hkernelCard] at hformula
  exact ⟨exponent, hformula ▸ Nat.mul_dvd_mul_right hrangeDivides (2 ^ exponent)⟩

theorem rank_one_two_group_aut_nine_not_dvd {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (hrank : twoRank Ambient ≤ 1) :
    ¬9 ∣ Nat.card (MulAut Ambient) := by
  obtain ⟨exponent, hdivides⟩ := two_group_two_generator_aut_card_dvd hpgroup
    (rank_one_two_group_generator_rank_le_two hpgroup hrank)
  intro hnine
  have hcoprime : Nat.Coprime 9 (2 ^ exponent) := (by norm_num : Nat.Coprime 9 2).pow_right exponent
  have hsmall : 9 ∣ 6 := hcoprime.dvd_mul_right.mp (hnine.trans hdivides)
  norm_num at hsmall

theorem nine_action_two_rank_two {Acting Ambient : Type groupUniverse} [Group Acting]
    [Group Ambient] [Finite Acting] [Finite Ambient] (hpgroup : IsPGroup 2 Ambient)
    (action : Acting →* MulAut Ambient) (hcard : 9 ∣ Nat.card action.range) :
    2 ≤ twoRank Ambient := by
  by_contra hnotRank
  have hsmall : twoRank Ambient ≤ 1 := by omega
  exact rank_one_two_group_aut_nine_not_dvd hpgroup hsmall
    (hcard.trans action.range.card_subgroup_dvd_card)

theorem nontrivial_odd_action_two_rank_two_all_primes {Acting Ambient : Type groupUniverse} [Group Acting]
    [Group Ambient] [Finite Acting] [Finite Ambient] {prime : ℕ} (hprime : prime.Prime)
    (hlarge : 3 < prime) (hpacting : IsPGroup prime Acting)
    (hpgroup : IsPGroup 2 Ambient) (action : Acting →* MulAut Ambient) (hnontrivial : action.range ≠ ⊥) :
    2 ≤ twoRank Ambient := by
  by_contra hnotRank
  have hsmall : twoRank Ambient ≤ 1 := by omega
  have hoptions := rank_one_two_group_aut_prime_support_exact hpgroup hsmall hprime
    (nontrivial_pGroup_action_prime_divides hprime hpacting action hnontrivial)
  rcases hoptions with htwo | hthree <;> omega

end CFSG.LargeEvenClassification.Helpers
