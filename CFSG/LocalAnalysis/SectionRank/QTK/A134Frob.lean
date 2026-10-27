module

import CFSG.GroupTheory.FrobeniusNormalComplement
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.SectionRank.QTK

open Subgroup

variable {S : Type} [Group S] [Finite S]

theorem two_dvd_card_of_simple (hs : IsSimpleGroup S) (hnonab : ∃ a b : S, a * b ≠ b * a) :
    2 ∣ Nat.card S := by
  by_contra h
  have hodd : Odd (Nat.card S) := Nat.odd_iff.mpr (by omega)
  have hsolv : Group.IsSolvable S := CFSG.FeitThompson.isSolvable_of_odd_natCard S hodd
  obtain ⟨a, b, hab⟩ := hnonab
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)

theorem exists_odd_prime_dvd_of_not_two_pow {m : ℕ} (hm : m ≠ 0) (h : ∀ a : ℕ, m ≠ 2 ^ a) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ m := by
  by_contra hcon
  push Not at hcon
  exact h _ (Nat.eq_prime_pow_of_unique_prime_dvd hm fun {d} hd hdm =>
    by_contra fun hd2 => hcon d hd hd2 hdm)

theorem exists_odd_prime_mem_normalizer [IsSimpleGroup S] (hnonab : ∃ a b : S, a * b ≠ b * a) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ ∃ R : Subgroup S, R ≠ ⊥ ∧ IsPGroup 2 R ∧
      ∃ x ∈ normalizer (R : Set S), orderOf x = r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 := two_dvd_card_of_simple (S := S) inferInstance hnonab
  have hno : ¬ ∃ N : Subgroup S, CFSG.GroupTheory.IsNormalPComplement 2 N := by
    rintro ⟨N, hNn, hcop, k, hk⟩
    rcases hNn.eq_bot_or_eq_top with rfl | rfl
    ·
      rw [index_bot] at hk
      have hS2 : IsPGroup 2 S := IsPGroup.of_card hk
      have : Group.IsNilpotent S := hS2.isNilpotent
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance a b)
    · rw [card_top] at hcop
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp (Nat.coprime_comm.mp hcop) h2
  rw [(CFSG.GroupTheory.frobenius_normal_p_complement (G := S) 2).1] at hno
  push Not at hno
  obtain ⟨Q, hQ2, hQ⟩ := hno
  have hcardN : Nat.card (normalizer (Q : Set S) ⧸
      (centralizer (Q : Set S)).subgroupOf (normalizer (Q : Set S))) ≠ 0 := Nat.card_pos.ne'
  obtain ⟨r, hr, hr2, hrd⟩ := exists_odd_prime_dvd_of_not_two_pow hcardN fun a ha =>
    hQ (IsPGroup.of_card ha)
  have hrN : r ∣ Nat.card (normalizer (Q : Set S)) :=
    hrd.trans (Subgroup.card_quotient_dvd_card _)
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(normalizer (Q : Set S))) r hrN
  refine ⟨r, hr, hr2, Q, ?_, hQ2, x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩
  rintro rfl
  apply hQ
  have htop : normalizer ((⊥ : Subgroup S) : Set S) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    rw [mem_normalizer_iff]
    intro h
    simp [Subgroup.mem_bot]
  have hctop : centralizer ((⊥ : Subgroup S) : Set S) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    rw [mem_centralizer_iff]
    intro h hh
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
    rw [hh, one_mul, mul_one]
  refine IsPGroup.of_card (n := 0) ?_
  rw [pow_zero, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, inferInstance⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  rw [QuotientGroup.eq]
  rw [Subgroup.mem_subgroupOf, hctop]
  exact Subgroup.mem_top _

end CFSG.SectionRank.QTK
