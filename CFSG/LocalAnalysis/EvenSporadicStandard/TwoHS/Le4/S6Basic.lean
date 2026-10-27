module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.Alperin

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

variable {G : Type*} [Group G]

theorem eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two {z x : G} (hz : orderOf z = 2)
    (hx : x ∈ zpowers z) : x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  have hmod : z ^ (k % (2 : ℤ)) = z ^ k := by simpa [hz] using zpow_mod_orderOf z k
  rw [← hmod]
  have : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases this with h | h <;> simp [h]

theorem eq_one_or_eq_sq_of_mem_zpowers {l g : G} (hl : orderOf l = 4) (hg : g ∈ zpowers l)
    (hg2 : g * g = 1) : g = 1 ∨ g = l ^ 2 := by
  by_cases h1 : g = 1
  · exact Or.inl h1
  · right
    have hg4 : g ^ 4 = 1 := by
      calc g ^ 4 = (g * g) * (g * g) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
        _ = 1 := by rw [hg2, mul_one]
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hg
    have hl4 : l ^ 4 = 1 := by simpa [hl] using pow_orderOf_eq_one l
    have hmod : l ^ (i % (4 : ℤ)) = l ^ i := by simpa [hl] using zpow_mod_orderOf l i
    rw [← hmod] at hg2 h1 ⊢
    have hj : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
    rcases hj with h | h | h | h
    · rw [h] at h1; simp at h1
    · rw [h] at hg2
      simp only [zpow_one] at hg2
      have := orderOf_dvd_of_pow_eq_one (show l ^ 2 = 1 by rwa [sq])
      rw [hl] at this
      omega
    · rw [h]; simp
    · rw [h] at hg2
      have h3 : l ^ (3 : ℤ) * l ^ (3 : ℤ) = l ^ 2 := by
        simp only [zpow_ofNat]
        calc l ^ 3 * l ^ 3 = l ^ 6 := by rw [← pow_add]
          _ = l ^ 4 * l ^ 2 := by rw [← pow_add]
          _ = l ^ 2 := by rw [hl4, one_mul]
      rw [h3] at hg2
      have := orderOf_dvd_of_pow_eq_one hg2
      rw [hl] at this
      omega

theorem eq_or_eq_inv_of_mem_zpowers_of_sq_ne_one {l g : G} (hl : orderOf l = 4)
    (hg : g ∈ zpowers l) (hg2 : g * g ≠ 1) : g = l ∨ g = l⁻¹ := by
  have hg4 : g ^ 4 = 1 := by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hg
    have hl4 : l ^ 4 = 1 := by simpa [hl] using pow_orderOf_eq_one l
    calc (l ^ i) ^ 4 = (l ^ 4) ^ i := by rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul,
          ← zpow_mul, mul_comm]
      _ = 1 := by rw [hl4, one_zpow]
  have hdvd : orderOf g ∣ 4 := orderOf_dvd_of_pow_eq_one hg4
  have hpos : 0 < orderOf g := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hle : orderOf g ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have h2 : orderOf g ≠ 1 := fun h => hg2 (by
    rw [orderOf_eq_one_iff.1 h]; simp)
  have h3 : orderOf g ≠ 2 := fun h => hg2 (by
    have := pow_orderOf_eq_one g
    rwa [h, sq] at this)
  have h4 : orderOf g = 4 := by
    obtain ⟨k, hk⟩ : ∃ k, orderOf g = k := ⟨_, rfl⟩
    rw [hk] at hdvd hpos hle h2 h3 ⊢
    interval_cases k <;> omega
  exact eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_four hl hg h4

theorem zpowers_cases {l y : G} (hl : orderOf l = 4) (hy : y ∈ zpowers l) :
    y = 1 ∨ y = l ∨ y = l⁻¹ ∨ y = l * l := by
  by_cases hyy : y * y = 1
  · rcases eq_one_or_eq_sq_of_mem_zpowers hl hy hyy with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (by rw [h, sq])))
  · rcases eq_or_eq_inv_of_mem_zpowers_of_sq_ne_one hl hy hyy with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))

end CFSG.EvenSporadicStandard.TwoHS
