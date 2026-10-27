module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GroupTheory.OrderBelowSixtySolvable

public section

namespace CFSG.EvenSporadicStandard.HNRecog.GH73

private theorem even_card_of_perfect {Y : Type*} [Group Y] [Finite Y] [Nontrivial Y]
    [Group.IsPerfect Y] : 2 ∣ Nat.card Y := by
  by_contra h
  have hodd : Odd (Nat.card Y) :=
    Nat.not_even_iff_odd.mp fun he => h (even_iff_two_dvd.mp he)
  exact Group.IsPerfect.not_isSolvable Y (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)

theorem perfect_sylow_two_not_cyclic {Y : Type*} [Group Y] [Finite Y] [Nontrivial Y]
    [Group.IsPerfect Y] (P : Sylow 2 Y) : ¬ IsCyclic (P : Subgroup Y) := by
  intro hP
  have heven : 2 ∣ Nat.card Y := even_card_of_perfect
  have hp : (Nat.card Y).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr heven
  have hcomp :
      (MonoidHom.transferSylow P (hP.normalizer_le_centralizer hp)).ker.IsComplement' P :=
    hP.isComplement' hp
  letI : IsMulCommutative (P : Subgroup Y) := hP.isMulCommutative
  have hker : (MonoidHom.transferSylow P (hP.normalizer_le_centralizer hp)).ker = ⊤ := by
    apply le_antisymm le_top
    rw [← Group.IsPerfect.commutator_eq_top (G := Y)]
    exact Abelianization.commutator_subset_ker
      (MonoidHom.transferSylow P (hP.normalizer_le_centralizer hp))
  have hbot : (P : Subgroup Y) = ⊥ := by
    rw [hker] at hcomp
    exact Subgroup.isComplement'_top_left.mp hcomp
  exact P.ne_bot_of_dvd_card heven hbot

theorem perfect_four_dvd_card {Y : Type*} [Group Y] [Finite Y] [Nontrivial Y]
    [Group.IsPerfect Y] : 4 ∣ Nat.card Y := by
  let P : Sylow 2 Y := default
  have heven : 2 ∣ Nat.card Y := even_card_of_perfect
  have hfac : Nat.card P = 2 ^ (Nat.card Y).factorization 2 := P.card_eq_multiplicity
  have hkpos : 0 < (Nat.card Y).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd (by norm_num) Nat.card_pos.ne' heven
  have hkne1 : (Nat.card Y).factorization 2 ≠ 1 := by
    intro hk
    have hPcard : Nat.card (P : Subgroup Y) = 2 := by
      rw [hfac, hk, pow_one]
    exact perfect_sylow_two_not_cyclic P (isCyclic_of_prime_card hPcard)
  have hle : 2 ≤ (Nat.card Y).factorization 2 := by omega
  have h4' : 2 ^ 2 ∣ Nat.card P := by
    rw [hfac]
    exact pow_dvd_pow 2 hle
  have h4 : 2 ^ 2 ∣ Nat.card Y := h4'.trans (P : Subgroup Y).card_subgroup_dvd_card
  rwa [show (4 : ℕ) = 2 ^ 2 by norm_num]

theorem perfect_sixty_le_card {Y : Type*} [Group Y] [Finite Y] [Nontrivial Y]
    [Group.IsPerfect Y] : 60 ≤ Nat.card Y := by
  by_contra h
  have hlt : Nat.card Y < 60 := Nat.not_le.mp h
  exact Group.IsPerfect.not_isSolvable Y
    (CFSG.GroupTheory.groups_order_below_sixty_solvable hlt)

theorem perfect_card_ne_eighty_four {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y] :
    Nat.card Y ≠ 84 := by
  intro hcard
  have hnt : Nontrivial Y := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  have hsol : Group.IsSolvable Y := by
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    let N : Sylow 7 Y := default
    haveI : Finite (Sylow 7 Y) := Sylow.finite_of_finiteIndex N
    have hNcard : Nat.card (N : Subgroup Y) = 7 := by
      obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq (p := 7) N.isPGroup'
      have hkpos : 0 < k := by
        have h7 : 7 ∣ Nat.card (N : Subgroup Y) := by
          have := N.dvd_card_of_dvd_card (p := 7) (by rw [hcard]; norm_num)
          simpa using this
        by_contra hk0
        rw [Nat.not_lt, Nat.le_zero] at hk0
        rw [hk, hk0, pow_zero] at h7
        norm_num at h7
      have hkle : k ≤ 1 := by
        have hdiv : 7 ^ k ∣ Nat.card Y := by
          rw [← hk]
          exact (N : Subgroup Y).card_subgroup_dvd_card
        rw [hcard] at hdiv
        by_contra hk1
        rw [Nat.not_le] at hk1
        have h2 : 2 ≤ k := by omega
        have h49 : 7 ^ 2 ∣ (84 : ℕ) := (pow_dvd_pow 7 h2).trans hdiv
        exact absurd h49 (by norm_num)
      rw [hk, show k = 1 by omega, pow_one]
    have hind : N.index = 12 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (N : Subgroup Y)
      have hq : Nat.card (Y ⧸ (N : Subgroup Y)) = 12 := by
        rw [hcard, hNcard] at h
        omega
      rw [Subgroup.index_eq_card, hq]
    have hdvd : Nat.card (Sylow 7 Y) ∣ 12 := by
      have h := N.card_dvd_index
      rwa [hind] at h
    have hmod : Nat.card (Sylow 7 Y) ≡ 1 [MOD 7] := card_sylow_modEq_one 7 Y
    haveI hsub : Subsingleton (Sylow 7 Y) := by
      rw [← Finite.card_le_one_iff_subsingleton]
      set n := Nat.card (Sylow 7 Y) with hn
      have hmod' : n % 7 = 1 := by
        have := hmod
        simpa [hn, Nat.ModEq] using this
      have hle' : n ≤ 12 := by
        simpa [hn] using Nat.le_of_dvd (by norm_num) hdvd
      have hpos : 1 ≤ n := by
        rw [hn]
        exact Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
      interval_cases n <;> omega
    have hNnormal : N.Normal := Sylow.normal_of_subsingleton N
    haveI : (N : Subgroup Y).Normal := hNnormal
    have hNsol : Group.IsSolvable (N : Subgroup Y) := by
      apply CFSG.GroupTheory.groups_order_below_sixty_solvable
      rw [hNcard]; norm_num
    have hQsol : Group.IsSolvable (Y ⧸ (N : Subgroup Y)) := by
      apply CFSG.GroupTheory.groups_order_below_sixty_solvable
      rw [← Subgroup.index_eq_card, hind]; norm_num
    exact Group.isSolvable_of_subgroup_quotient (N : Subgroup Y)
  exact Group.IsPerfect.not_isSolvable Y hsol

theorem exists_sylow_dihedral_two_of_card_four_mul_odd {Y : Type*} [Group Y] [Finite Y]
    [Group.IsPerfect Y] {m : ℕ} (hm : Odd m) (hcard : Nat.card Y = 4 * m) :
    ∃ P : Sylow 2 Y, Nonempty ((P : Subgroup Y) ≃* DihedralGroup 2) := by
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hcard
    exact Nat.card_pos.ne' hcard
  have hnt : Nontrivial Y := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    nlinarith
  let P : Sylow 2 Y := default
  have hm2 : m.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      rw [← even_iff_two_dvd]
      exact Nat.not_even_iff_odd.mpr hm)
  have h4fac : (4 : ℕ).factorization 2 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.factorization_pow_self (p := 2) (n := 2) (by norm_num : Nat.Prime 2)
  have hfac : (4 * m).factorization 2 = 2 := by
    rw [Nat.factorization_mul (a := 4) (b := m) (by norm_num) hm0]
    simp [h4fac, hm2]
  have hPcard : Nat.card (P : Subgroup Y) = 4 := by
    have h := P.card_eq_multiplicity
    rw [hcard] at h
    rw [h, hfac]
    norm_num
  have hnotcyc : ¬ IsCyclic (P : Subgroup Y) := perfect_sylow_two_not_cyclic P
  haveI hntP : Nontrivial (P : Subgroup Y) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hPcard]
    norm_num
  have hexp : Monoid.exponent (P : Subgroup Y) = 2 := by
    rw [Monoid.exponent_eq_prime_iff (by norm_num : Nat.Prime 2)]
    intro g hg
    have hdvd : orderOf g ∣ 4 := by
      have := orderOf_dvd_natCard g
      rwa [hPcard] at this
    have hdvd' : orderOf g ∣ 2 ^ 2 := by simpa using hdvd
    obtain ⟨k, hk_le, hk⟩ :=
      (Nat.dvd_prime_pow (p := 2) (by norm_num : Nat.Prime 2)).mp hdvd'
    interval_cases k
    · exact absurd (orderOf_eq_one_iff.mp (by simpa using hk)) hg
    · simpa using hk
    · have hcyc : IsCyclic (P : Subgroup Y) :=
        isCyclic_of_orderOf_eq_card g (by rw [hk, hPcard]; norm_num)
      exact absurd hcyc hnotcyc
  haveI : IsKleinFour (P : Subgroup Y) := ⟨hPcard, hexp⟩
  exact ⟨P, IsKleinFour.nonempty_mulEquiv⟩

end CFSG.EvenSporadicStandard.HNRecog.GH73
