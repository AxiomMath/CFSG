module

public import CFSG.GH74.Uniqueness.Section172Defs
public import CFSG.GH74.Uniqueness.Section12BenderDict

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem factorization_two_mul_two_pow {m k : ℕ} (hm : Odd m) :
    (m * 2 ^ k).factorization 2 = k := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  rw [Nat.factorization_mul hm0 (pow_ne_zero _ two_ne_zero), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by
      intro h
      exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h))]
  simp

theorem ZDSetup.lemma172P
    (S : ZDSetup X Z M) : Lemma172PStmt Z M := by
  intro c n i e hB
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F : Subgroup X := cenHull Z c.u with hF
  have hP' : Nat.card c.P = 2 ^ (Nat.card ↥(F ⊓ M)).factorization 2 := c.hP.card_eq
  rw [hP']
  have hn2 : 2 ≤ n := hB.bender.two_le.2
  have hZodd : Odd (Nat.card (center ↥F)) := by
    have h1 := odd_card_pPrimeCoreIn F
    rw [hB.core, Subgroup.card_map_of_injective F.subtype_injective] at h1
    exact h1
  have hq1 : Odd (2 ^ n - 1) := by
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = 2 * (k + 1) := ⟨2 ^ (n - 1) - 1, by
      have : 0 < 2 ^ (n - 1) := pow_pos (by norm_num) _
      rw [Nat.sub_add_cancel this, ← pow_succ']
      congr 1
      omega⟩
    exact ⟨k, by omega⟩
  have heodd : Odd e := by
    rcases hB.bender.cases' with ⟨-, he, -⟩ | ⟨-, he, -⟩ | ⟨-, he, -⟩
    · rw [he]; exact odd_one
    · rw [he]; exact odd_one
    · rw [he]
      have hodd : Odd (2 ^ n + 1) := by
        have : Even (2 ^ n) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
        exact this.add_one
      exact Odd.of_dvd_nat hodd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right 3 (2 ^ n + 1)))
  have hidx := BenderSub.index_eq S hB
  have h1 := Subgroup.card_mul_index ((M ⊓ F).subgroupOf F)
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥F)
  have h3 := hB.bender.card_eq
  have hcard : Nat.card ↥(F ⊓ M) =
      Nat.card (center ↥F) * ((2 ^ n - 1) * e) * 2 ^ (n * i) := by
    have hpos : 0 < (2 ^ n) ^ i + 1 := Nat.succ_pos _
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [inf_comm] at h1
    rw [h1]
    have hF' : Nat.card ↥F = Nat.card (center ↥F) * Nat.card (↥F ⧸ center ↥F) := by
      rw [h2, mul_comm]
    rw [hF', h3, pow_mul]
    ring
  rw [hcard, factorization_two_mul_two_pow (by
    have := hZodd
    exact hZodd.mul (hq1.mul heodd)), pow_mul]

end CFSG.GH74.Uniqueness
