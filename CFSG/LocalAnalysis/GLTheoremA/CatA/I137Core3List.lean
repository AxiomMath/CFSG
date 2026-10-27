module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I137C3

open CFSG.Yardstones.Md0ec50421ce4 TauCeti CFSG.Open
  CFSG.HardMathSupport.Solomon.Coordinator.I1420

namespace Core3Arith

theorem orderA_two (q : ℕ) :
    orderA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) := by
  have h : Finset.Icc 2 (2 + 1) = {2, 3} := by decide
  simp [orderA, h, Finset.prod_pair]

theorem orderTwistedA_two (q : ℕ) :
    orderTwistedA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1) := by
  have h : Finset.Icc 2 (2 + 1) = {2, 3} := by decide
  simp [orderTwistedA, h, Finset.prod_pair, Nat.even_iff]

theorem pow_three_dvd_orderA_two (q : ℕ) : q ^ 3 ∣ orderA 2 q := by
  rw [orderA_two]
  have hg : Nat.gcd 3 (q - 1) ∣ (q ^ 2 - 1) * (q ^ 3 - 1) :=
    ((Nat.gcd_dvd_right 3 (q - 1)).trans (sub_one_dvd_sq_sub_one q)).trans (Dvd.intro _ rfl)
  rw [Nat.mul_div_assoc _ hg]
  exact Dvd.intro _ rfl

theorem pow_three_dvd_orderTwistedA_two {q : ℕ} (hq : 1 ≤ q) : q ^ 3 ∣ orderTwistedA 2 q := by
  rw [orderTwistedA_two]
  have hg : Nat.gcd 3 (q + 1) ∣ (q ^ 2 - 1) * (q ^ 3 + 1) :=
    ((Nat.gcd_dvd_right 3 (q + 1)).trans (add_one_dvd_sq_sub_one q hq)).trans (Dvd.intro _ rfl)
  rw [Nat.mul_div_assoc _ hg]
  exact Dvd.intro _ rfl

theorem two_pow_mod_three_of_even {e : ℕ} (he : Even e) : 2 ^ e % 3 = 1 := by
  obtain ⟨k, rfl⟩ := he
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem two_pow_mod_three_of_odd {e : ℕ} (he : Odd e) : 2 ^ e % 3 = 2 := by
  obtain ⟨k, rfl⟩ := he
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem even_of_two_pow_mod_three {e : ℕ} (h : 2 ^ e % 3 = 1) : Even e := by
  rcases Nat.even_or_odd e with he | he
  · exact he
  · have := two_pow_mod_three_of_odd he
    omega

theorem odd_of_two_pow_mod_three {e : ℕ} (h : 2 ^ e % 3 = 2) : Odd e := by
  rcases Nat.even_or_odd e with he | he
  · have := two_pow_mod_three_of_even he
    omega
  · exact he

end Core3Arith

open Core3Arith

@[expose] def list93FixedOrders : List ℕ :=
  [174182400, 1056706560, 4329310519296, 34693789777920, 9196830720, 211341312,
    264905352699586176614400]

section Certified

theorem card_list93three {Q₀ : Type} [Group Q₀] [Finite Q₀]
    (h : catalogIs Q₀ (S9.isList93 3)) :
    Nat.card Q₀ ∈ list93FixedOrders ∨
      (∃ e : ℕ, 2 ≤ e ∧ Even e ∧ Nat.card Q₀ = orderA 2 (2 ^ e) ∧
        (e = 2 → catalogIs Q₀ S9.isL3four)) ∨
      (∃ e : ℕ, 3 ≤ e ∧ Odd e ∧ Nat.card Q₀ = orderTwistedA 2 (2 ^ e)) := by
  obtain ⟨d, hne, hcases⟩ := list93three_cases h
  have hcard := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds d Q₀ hne
  rcases hcases with ⟨q, hd, hq⟩ | ⟨q, hd, hq⟩ | ⟨q, hd, hq⟩ | ⟨q, hd, hq⟩ | ⟨q, hd, hq⟩ |
    ⟨q, hd, hq⟩ | hd | ⟨q, hd, hp, hq⟩ | ⟨q, hd, hp, hq⟩
  · left
    rw [hcard, hd]
    simp only [lieOrderFormula, hq]
    decide +kernel
  · left
    rw [hcard, hd]
    simp only [lieOrderFormula, hq]
    decide +kernel
  · left
    rw [hcard, hd]
    simp only [lieOrderFormula, hq]
    decide +kernel
  · left
    rw [hcard, hd]
    simp only [lieOrderFormula, hq]
    decide +kernel
  · left
    rw [hcard, hd]
    simp only [lieOrderFormula, hq]
    decide +kernel
  · left
    rw [hcard, hd]
    simp only [lieOrderFormula, hq]
    decide +kernel
  · left
    rw [hcard, hd]
    simp only [lieOrderFormula]
    decide +kernel
  · right; left
    have hc : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hp]
    have hev : Even q.exponent := even_of_two_pow_mod_three (hc ▸ hq)
    have hpos := q.exponent_pos
    refine ⟨q.exponent, ?_, hev, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := hev
      omega
    · rw [hcard, hd]
      simp only [lieOrderFormula]
      rw [hc]
    · intro h2
      refine ⟨CFSGIndex.lie d, ?_, hne⟩
      simp only [S9.isL3four, onLie, hd]
      rw [hc, h2]
      norm_num
  · right; right
    have hc : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hp]
    have hodd : Odd q.exponent := odd_of_two_pow_mod_three (hc ▸ hq)
    have h3 : 3 ≤ q.card := by
      have hv := d.2
      rw [hd] at hv
      exact ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).2 rfl
    refine ⟨q.exponent, ?_, hodd, ?_⟩
    · obtain ⟨k, hk⟩ := hodd
      rcases k with _ | k
      · rw [hc, hk] at h3
        norm_num at h3
      · omega
    · rw [hcard, hd]
      simp only [lieOrderFormula]
      rw [hc]

theorem card_list93three_two_part {Q₀ : Type} [Group Q₀] [Finite Q₀]
    (h : catalogIs Q₀ (S9.isList93 3)) :
    128 ∣ Nat.card Q₀ ∨ catalogIs Q₀ S9.isL3four := by
  rcases card_list93three h with hfix | ⟨e, he2, hev, hcard, hcat⟩ | ⟨e, he3, hodd, hcard⟩
  · left
    have key : ∀ n ∈ list93FixedOrders, 128 ∣ n := by decide +kernel
    exact key _ hfix
  · by_cases he : e = 2
    · exact Or.inr (hcat he)
    · left
      have h4 : 4 ≤ e := by
        obtain ⟨k, hk⟩ := hev
        omega
      have h37 : (2 : ℕ) ^ 7 ∣ (2 ^ e) ^ 3 := by
        rw [← pow_mul, mul_comm]
        exact pow_dvd_pow 2 (by omega)
      rw [hcard]
      exact h37.trans (pow_three_dvd_orderA_two _)
  · left
    have h37 : (2 : ℕ) ^ 7 ∣ (2 ^ e) ^ 3 := by
      rw [← pow_mul, mul_comm]
      exact pow_dvd_pow 2 (by omega)
    rw [hcard]
    exact h37.trans (pow_three_dvd_orderTwistedA_two Nat.one_le_two_pow)

theorem two_pow_six_dvd_card_list93three {Q₀ : Type} [Group Q₀] [Finite Q₀]
    (h : catalogIs Q₀ (S9.isList93 3)) : 64 ∣ Nat.card Q₀ := by
  rcases card_list93three h with hfix | ⟨e, he2, hev, hcard, hcat⟩ | ⟨e, he3, hodd, hcard⟩
  · have key : ∀ n ∈ list93FixedOrders, 64 ∣ n := by decide +kernel
    exact key _ hfix
  · have h36 : (2 : ℕ) ^ 6 ∣ (2 ^ e) ^ 3 := by
      rw [← pow_mul, mul_comm]
      exact pow_dvd_pow 2 (by omega)
    rw [hcard]
    exact h36.trans (pow_three_dvd_orderA_two _)
  · have h36 : (2 : ℕ) ^ 6 ∣ (2 ^ e) ^ 3 := by
      rw [← pow_mul, mul_comm]
      exact pow_dvd_pow 2 (by omega)
    rw [hcard]
    exact h36.trans (pow_three_dvd_orderTwistedA_two Nat.one_le_two_pow)

theorem card_list93three_ge {Q₀ : Type} [Group Q₀] [Finite Q₀]
    (h : catalogIs Q₀ (S9.isList93 3)) :
    5515776 ≤ Nat.card Q₀ ∨ catalogIs Q₀ S9.isL3four := by
  have hpos : 0 < Nat.card Q₀ := Nat.card_pos
  rcases card_list93three h with hfix | ⟨e, he2, hev, hcard, hcat⟩ | ⟨e, he3, hodd, hcard⟩
  · left
    have key : ∀ n ∈ list93FixedOrders, 5515776 ≤ n := by decide +kernel
    exact key _ hfix
  · by_cases he : e = 2
    · exact Or.inr (hcat he)
    · left
      have h4 : 4 ≤ e := by
        obtain ⟨k, hk⟩ := hev
        omega
      by_cases h8 : 8 ≤ e
      · have h2 : (2 : ℕ) ^ 24 ≤ 2 ^ (3 * e) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h3 : (2 : ℕ) ^ (3 * e) ∣ Nat.card Q₀ := by
          rw [hcard, mul_comm, pow_mul]
          exact pow_three_dvd_orderA_two _
        have := Nat.le_of_dvd hpos h3
        omega
      · obtain ⟨k, hk⟩ := hev
        have he46 : e = 4 ∨ e = 6 := by omega
        rcases he46 with rfl | rfl <;> (rw [hcard]; decide +kernel)
  · left
    by_cases h9 : 9 ≤ e
    · have h2 : (2 : ℕ) ^ 27 ≤ 2 ^ (3 * e) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : (2 : ℕ) ^ (3 * e) ∣ Nat.card Q₀ := by
        rw [hcard, mul_comm, pow_mul]
        exact pow_three_dvd_orderTwistedA_two Nat.one_le_two_pow
      have := Nat.le_of_dvd hpos h3
      omega
    · obtain ⟨k, hk⟩ := hodd
      have he357 : e = 3 ∨ e = 5 ∨ e = 7 := by omega
      rcases he357 with rfl | rfl | rfl <;> (rw [hcard]; decide +kernel)

theorem core3Group_of_card_lt {S : Type} [Group S] [Finite S] (h : Nat.card S < 5515776) :
    Core3Group S := by
  intro T A _ _ _ Q₀ _ ⟨f, hf⟩ hQ
  have : Finite Q₀ := Finite.of_surjective f hf
  rcases card_list93three_ge hQ with hge | hL3
  · have hle : Nat.card Q₀ ≤ Nat.card S :=
      Nat.le_of_dvd Nat.card_pos ((card_dvd_of_surjective f hf).trans
        (Subgroup.card_subgroup_dvd_card A))
    omega
  · exact hL3

end Certified

end CFSG.LocalAnalysis.GLTheoremA.I137C3

end
