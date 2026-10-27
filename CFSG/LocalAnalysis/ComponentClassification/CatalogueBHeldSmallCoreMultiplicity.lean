module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreKernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreCharacteristic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.ComponentClassification.CatalogueBHeldSmallCore

@[expose] def SmallMultiplicity (n : ℕ) : Prop :=
  n.factorization 3 ≤ 2 ∧ ∀ p : ℕ, p.Prime → p ≠ 3 → n.factorization p ≤ 1

theorem smallMultiplicity_of_dvd {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hdivides : m ∣ n) (hsmall : SmallMultiplicity n) : SmallMultiplicity m := by
  have hle := (Nat.factorization_le_iff_dvd hm hn).mpr hdivides
  exact ⟨(hle 3).trans hsmall.1, fun p hp hpthree =>
    (hle p).trans (hsmall.2 p hp hpthree)⟩

theorem elementaryAbelian_card_prime_or_nine (H : Type*) [Group H] [Finite H]
    [Nontrivial H] (p : ℕ) [Fact p.Prime] [CFSG.IsElementaryAbelian p H]
    (hsmall : SmallMultiplicity (Nat.card H)) : Nat.card H = p ∨ p = 3 ∧ Nat.card H = 9 := by
  obtain ⟨n, hn, hcard⟩ :=
    ((CFSG.IsElementaryAbelian.isPGroup p H).nontrivial_iff_card).mp inferInstance
  have hp : p.Prime := Fact.out
  by_cases hpthree : p = 3
  · have hbound : n ≤ 2 := by
      have hbound := hsmall.1
      rw [hcard, ← hpthree, Nat.factorization_pow_self hp] at hbound
      exact hbound
    have hnvalues : n = 1 ∨ n = 2 := by omega
    rcases hnvalues with rfl | rfl
    · exact Or.inl (by simpa using hcard)
    · exact Or.inr ⟨hpthree, by simpa [hpthree] using hcard⟩
  · have hbound : n ≤ 1 := by
      have hbound := hsmall.2 p hp hpthree
      rw [hcard, Nat.factorization_pow_self hp] at hbound
      exact hbound
    have hn1 : n = 1 := by omega
    exact Or.inl (by simpa [hn1] using hcard)

theorem elementaryAbelian_automorphism_solvable (H : Type*) [Group H] [Finite H]
    [Nontrivial H] (p : ℕ) [Fact p.Prime] [CFSG.IsElementaryAbelian p H]
    (hsmall : SmallMultiplicity (Nat.card H)) : Group.IsSolvable (MulAut H) := by
  rcases elementaryAbelian_card_prime_or_nine H p hsmall with hprime | ⟨rfl, hnine⟩
  · let : IsCyclic H := isCyclic_of_prime_card hprime
    exact cyclic_automorphism_solvable H
  · exact elementaryAbelian_nine_automorphism_solvable H hnine

theorem automorphism_solvable_of_smallMultiplicity (M : Type*) [Group M] [Finite M]
    [Group.IsSolvable M] (hsmall : SmallMultiplicity (Nat.card M)) :
    Group.IsSolvable (MulAut M) := by
  induction hcard : Nat.card M using Nat.strong_induction_on generalizing M with
  | h cardinal hinduction =>
    cases subsingleton_or_nontrivial M with
    | inl htrivial =>
      let : Subsingleton M := htrivial
      let : Subsingleton (MulAut M) := ⟨fun f g => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
      infer_instance
    | inr hnontrivial =>
      let : Nontrivial M := hnontrivial
      obtain ⟨A, p, hAchar, hAnonzero, hp, hAelementary⟩ :=
        exists_characteristic_elementaryAbelian M
      let : A.Characteristic := hAchar
      let : CFSG.IsElementaryAbelian p A := hAelementary
      let : Fact p.Prime := ⟨hp⟩
      let : Nontrivial A := A.nontrivial_iff_ne_bot.mpr hAnonzero
      let : Group.IsSolvable (MulAut A) := elementaryAbelian_automorphism_solvable A p
        (smallMultiplicity_of_dvd (ne_of_gt Nat.card_pos) (ne_of_gt Nat.card_pos)
          A.card_subgroup_dvd_card hsmall)
      have hquotientSmall : SmallMultiplicity (Nat.card (M ⧸ A)) :=
        smallMultiplicity_of_dvd (ne_of_gt Nat.card_pos) (ne_of_gt Nat.card_pos)
          A.card_quotient_dvd_card hsmall
      have hquotientLess : Nat.card (M ⧸ A) < cardinal := by
        have hcardGreater : 1 < Nat.card A := A.one_lt_card_iff_ne_bot.mpr hAnonzero
        have hquotientPositive : 0 < Nat.card (M ⧸ A) := Nat.card_pos
        rw [← hcard, A.card_eq_card_quotient_mul_card_subgroup]
        exact (Nat.lt_mul_iff_one_lt_right hquotientPositive).mpr hcardGreater
      let : Group.IsSolvable (MulAut (M ⧸ A)) :=
        hinduction (Nat.card (M ⧸ A)) hquotientLess (M ⧸ A) hquotientSmall rfl
      exact automorphism_solvable_of_sections A

theorem small_prime_multiplicity_solvable_automorphisms
    (M : Type*) [Group M] [Finite M] [Group.IsSolvable M]
    (hthree : (Nat.card M).factorization 3 ≤ 2)
    (hother : ∀ p : ℕ, p.Prime → p ≠ 3 → (Nat.card M).factorization p ≤ 1) :
    Group.IsSolvable (MulAut M) :=
  automorphism_solvable_of_smallMultiplicity M ⟨hthree, hother⟩

end CFSG.ComponentClassification.CatalogueBHeldSmallCore
