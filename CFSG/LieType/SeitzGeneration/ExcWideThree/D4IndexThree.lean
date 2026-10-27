module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4Orders
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4Fixed

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.Timmesfeld.ExceptionalOrders

section IndexThree

private theorem not_dvd_geomSum_three {q : ℕ} (h3q : 3 ∣ q) {n : ℕ} (hn : 1 ≤ n) :
    ¬ 3 ∣ geomSum n 1 q := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  intro h
  rw [geomSum, Finset.sum_range_succ'] at h
  simp only [one_mul, pow_zero] at h
  have hsum : 3 ∣ ∑ i ∈ Finset.range k, q ^ (i + 1) :=
    Finset.dvd_sum fun i _ => dvd_pow h3q (by omega)
  have h1 : 3 ∣ 1 := by
    have h' := Nat.dvd_sub h hsum
    rwa [show (∑ i ∈ Finset.range k, q ^ (i + 1)) + 1 -
      ∑ i ∈ Finset.range k, q ^ (i + 1) = 1 by omega] at h'
  exact Nat.prime_three.not_dvd_one h1

theorem card_adjointGroup_D4_char_three
    {F : Type} [Field F] [Finite F] {m : ℕ}
    (hF : Nat.card F = 3 ^ m) (hm : 1 ≤ m) :
    ∃ u : ℕ, ¬ 3 ∣ u ∧ Nat.card (adjointGroup Tag.D4 F) = 3 ^ (12 * m) * u := by
  have h3q : 3 ∣ Nat.card F := by rw [hF]; exact dvd_pow_self 3 (by omega)
  have hq1 : 1 ≤ Nat.card F := Nat.card_pos
  have h2 := not_dvd_geomSum_three h3q (n := 2) (by norm_num)
  have h4 := not_dvd_geomSum_three h3q (n := 4) (by norm_num)
  have h6 := not_dvd_geomSum_three h3q (n := 6) (by norm_num)
  have htorus : ¬ 3 ∣ Nat.card (torusGroup Tag.D4 F) := by
    intro h
    have hdiv : 3 ∣ (Nat.card F - 1) ^ 4 :=
      h.trans (Dvd.intro _ (card_torusGroup_mul (τ := Tag.D4) (K := F)))
    have hsub : 3 ∣ Nat.card F - 1 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdiv
    have h1 : 3 ∣ 1 := by
      have h' := Nat.dvd_sub h3q hsub
      rwa [Nat.sub_sub_self hq1] at h'
    exact Nat.prime_three.not_dvd_one h1
  refine ⟨Nat.card (torusGroup Tag.D4 F) *
    (geomSum 2 1 (Nat.card F) * geomSum 4 1 (Nat.card F) *
      geomSum 4 1 (Nat.card F) * geomSum 6 1 (Nat.card F)), ?_, ?_⟩
  · intro h
    rcases (Nat.prime_three.dvd_mul).1 h with h | h
    · exact htorus h
    rcases (Nat.prime_three.dvd_mul).1 h with h | h
    · rcases (Nat.prime_three.dvd_mul).1 h with h | h
      · rcases (Nat.prime_three.dvd_mul).1 h with h | h
        · exact h2 h
        · exact h4 h
      · exact h4 h
    · exact h6 h
  · rw [card_adjointGroup_D4_eq, hF, ← pow_mul, Nat.mul_comm m 12]
    ring

theorem three_dvd_index_subfieldGroup_D4
    {K : Type} [Field K] [Finite K] {e : ℕ}
    (hK : Nat.card K = 3 ^ (e * 3)) (he : 1 ≤ e) (T : K ≃+* K) (hT3 : T ^ 3 = 1)
    (hcard : Nat.card (fixSubfield T) = 3 ^ e) :
    3 ∣ (subfieldGroup Tag.D4 T).index := by
  obtain ⟨u, h3u, hcardG⟩ :=
    card_adjointGroup_D4_char_three (F := K) (m := e * 3) hK (by omega)
  obtain ⟨u', h3u', hcardH⟩ :=
    card_adjointGroup_D4_char_three (F := ↥(fixSubfield T)) (m := e) hcard he
  have hH : Nat.card (subfieldGroup Tag.D4 T) = 3 ^ (12 * e) * u' := by
    rw [card_subfieldGroup_D4 T hT3]
    exact hcardH
  have hmain : (subfieldGroup Tag.D4 T).index * u' = 3 ^ (24 * e) * u := by
    have h := Subgroup.index_mul_card (subfieldGroup Tag.D4 T)
    rw [hH, hcardG] at h
    rw [show 12 * (e * 3) = 12 * e + 24 * e by ring, pow_add] at h
    refine Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num : (0 : ℕ) < 3) (12 * e)) ?_
    calc ((subfieldGroup Tag.D4 T).index * u') * 3 ^ (12 * e)
        = (subfieldGroup Tag.D4 T).index * (3 ^ (12 * e) * u') := by ring
      _ = (3 ^ (12 * e) * 3 ^ (24 * e)) * u := h
      _ = (3 ^ (24 * e) * u) * 3 ^ (12 * e) := by ring
  have h3 : 3 ∣ (subfieldGroup Tag.D4 T).index * u' := by
    rw [hmain]
    exact dvd_mul_of_dvd_left (dvd_pow_self 3 (by omega : 24 * e ≠ 0)) u
  rcases (Nat.prime_three.dvd_mul).1 h3 with h | h
  · exact h
  · exact absurd h h3u'

end IndexThree

end CFSG.LieType.SeitzGeneration.ExcWideThree
