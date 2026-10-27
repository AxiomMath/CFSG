module

public import CFSG.LocalAnalysis.SectionRank.QTK.A134ListSporA

public section

namespace CFSG.SectionRank.QTK

open scoped commutatorElement

variable {S : Type} [Group S] [Finite S] {x y h : S}

theorem oddLocalWitness_of_cubic_J4 (hx : x ^ 3 = 1) (hz : ⁅x, y⁆ ≠ 1)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (h1 : h * x * h⁻¹ = x ^ 2 * y ^ 0 * ⁅x, y⁆ ^ 0) (h3 : h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 1) :
    OddLocalWitness S := by
  simp only [pow_zero, pow_one, mul_one] at h1 h3
  have hcx : MulAut.conj h x = x ^ 2 := by rw [MulAut.conj_apply, h1]
  have h2 : Commute (h ^ 2 ^ 1) x := by
    rw [commute_iff_conj_eq, pow_one, conj_sq_apply, hcx, map_pow, hcx, ← pow_mul,
      pow_eq_pow_mod _ hx]
    norm_num
  have hn : ¬ Commute h x := fun hc => hz (by
    rw [commute_iff_conj_eq, hcx, pow_two, mul_eq_right] at hc
    rw [hc, commutatorElement_one_left])
  exact ⟨3, Nat.prime_three, by norm_num, two_le_pRank_of_cubic Nat.prime_three hx hz hzx hzy,
    one_le_localRank_of_commute_even (by norm_num)
      (commute_iff_conj_eq.2 (by rw [MulAut.conj_apply, h3]))
      (orderOf_commutator_of_cubic Nat.prime_three hx hz hzx) (even_orderOf_of_commute_pow 1 h2 hn)⟩

theorem oddLocalWitness_of_square_HS (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : x * y = y * x)
    (hc : Nat.card (Subgroup.closure ({x, y} : Set S)) = 3 ^ 2)
    (h1 : h * x * h⁻¹ = x ^ 1 * y ^ 0) (h2 : h * y * h⁻¹ = x ^ 2 * y ^ 2) :
    OddLocalWitness S := by
  have hxy' : Commute x y := hxy
  have hcx : MulAut.conj h x = x ^ 1 * y ^ 0 := by rw [MulAut.conj_apply, h1]
  have hcy : MulAut.conj h y = x ^ 2 * y ^ 2 := by rw [MulAut.conj_apply, h2]
  have hx1 : x ≠ 1 := fun h0 =>
    (by norm_num : ¬ (3 ^ 2 : ℕ) ≤ 3) (hc ▸ card_closure_pair_le (x := x) (by norm_num) hy 0
      (by rw [h0, pow_zero]))
  have hhx : Commute h x := commute_iff_conj_eq.2 (by rw [hcx, pow_one, pow_zero, mul_one])
  have hsq : Commute (h ^ 2 ^ 1) y := by
    rw [commute_iff_conj_eq, pow_one, conj_sq_apply, hcy, conj_mono hxy' hx hy _ hcx hcy]
    norm_num
  have hn : ¬ Commute h y := fun hc' => by
    rw [commute_iff_conj_eq, hcy] at hc'
    have h3 : x ^ 2 * y = 1 := by
      have e : x ^ 2 * y * y = 1 * y := by rw [one_mul, mul_assoc, ← pow_two]; exact hc'
      exact mul_right_cancel e
    have hyx : y = x ^ 1 := by
      rw [eq_inv_of_mul_eq_one_right h3, pow_one]
      exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact hx)
    have hle := card_closure_pair_le (x := y) (by norm_num) hx 1 hyx
    rw [Set.pair_comm] at hle
    exact (by norm_num : ¬ (3 ^ 2 : ℕ) ≤ 3) (hc ▸ hle)
  exact ⟨3, Nat.prime_three, by norm_num, two_le_pRank_of_square Nat.prime_three hx hy hxy hc,
    one_le_localRank_of_commute_even (by norm_num) hhx (orderOf_eq_prime hx hx1)
      (even_orderOf_of_commute_pow 1 hsq hn)⟩

theorem oddLocalWitness_of_cubic_He (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : ⁅x, y⁆ ≠ 1)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (h1 : h * x * h⁻¹ = x ^ 0 * y ^ 2 * ⁅x, y⁆ ^ 0) (h2 : h * y * h⁻¹ = x ^ 1 * y ^ 0 * ⁅x, y⁆ ^ 0)
    (h3 : h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 1) : OddLocalWitness S := by
  simp only [pow_zero, pow_one, mul_one, one_mul] at h1 h2 h3
  have hcx : MulAut.conj h x = y ^ 2 := by rw [MulAut.conj_apply, h1]
  have hcy : MulAut.conj h y = x := by rw [MulAut.conj_apply, h2]
  have hy4 : y ^ (2 * 2) = y := by rw [show 2 * 2 = 3 + 1 from rfl, pow_succ, hy, one_mul]
  have h4 : Commute (h ^ 2 ^ 2) x := by
    rw [commute_iff_conj_eq, show h ^ 2 ^ 2 = (h ^ 2) ^ 2 by rw [← pow_mul]; rfl, conj_sq_apply,
      conj_sq_apply, conj_sq_apply, hcx, map_pow, hcy, map_pow, hcx, ← pow_mul, hy4, hcy]
  have hn : ¬ Commute h x := fun hc => hz (by
    rw [commute_iff_conj_eq, hcx] at hc
    rw [← hc]
    exact commutatorElement_eq_one_iff_mul_comm.2 ((Commute.refl y).pow_left 2).eq)
  exact ⟨3, Nat.prime_three, by norm_num, two_le_pRank_of_cubic Nat.prime_three hx hz hzx hzy,
    one_le_localRank_of_commute_even (by norm_num)
      (commute_iff_conj_eq.2 (by rw [MulAut.conj_apply, h3]))
      (orderOf_commutator_of_cubic Nat.prime_three hx hz hzx) (even_orderOf_of_commute_pow 2 h4 hn)⟩

theorem oddLocalWitness_of_square_J2 (hx : x ^ 5 = 1) (hy : y ^ 5 = 1) (hxy : x * y = y * x)
    (hc : Nat.card (Subgroup.closure ({x, y} : Set S)) = 5 ^ 2)
    (h1 : h * x * h⁻¹ = x ^ 0 * y ^ 4) (h2 : h * y * h⁻¹ = x ^ 4 * y ^ 0) :
    OddLocalWitness S := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hxy' : Commute x y := hxy
  have hcx : MulAut.conj h x = x ^ 0 * y ^ 4 := by rw [MulAut.conj_apply, h1]
  have hcy : MulAut.conj h y = x ^ 4 * y ^ 0 := by rw [MulAut.conj_apply, h2]
  have hnot : ∀ n : ℕ, x = y ^ n → False := fun n hn =>
    (by norm_num : ¬ (5 ^ 2 : ℕ) ≤ 5) (hc ▸ card_closure_pair_le (by norm_num) hy n hn)
  have hw : Commute h (x ^ 1 * y ^ 4) := commute_iff_conj_eq.2 (by
    rw [conj_mono hxy' hx hy _ hcx hcy])
  have hw1 : x ^ 1 * y ^ 4 ≠ 1 := fun h0 => hnot 1 (by
    rw [pow_one] at h0 ⊢
    rw [eq_inv_of_mul_eq_one_left h0]
    exact inv_eq_of_mul_eq_one_left (by rw [← pow_succ']; exact hy))
  have hw5 : (x ^ 1 * y ^ 4) ^ 5 = 1 := by
    rw [(hxy'.pow_pow 1 4).mul_pow, ← pow_mul, ← pow_mul, pow_eq_pow_mod _ hx,
      pow_eq_pow_mod _ hy]
    norm_num
  have hsq : Commute (h ^ 2 ^ 1) x := by
    rw [commute_iff_conj_eq, pow_one, conj_sq_apply, hcx, conj_mono hxy' hx hy _ hcx hcy]
    norm_num
  have hn : ¬ Commute h x := fun hc' => by
    rw [commute_iff_conj_eq, hcx, pow_zero, one_mul] at hc'
    exact hnot 4 hc'.symm
  exact ⟨5, Nat.prime_five, by norm_num, two_le_pRank_of_square Nat.prime_five hx hy hxy hc,
    one_le_localRank_of_commute_even (by norm_num) hw (orderOf_eq_prime hw5 hw1)
      (even_orderOf_of_commute_pow 1 hsq hn)⟩

theorem oddLocalWitness_of_cubic_Ru (hx : x ^ 5 = 1) (hz : ⁅x, y⁆ ≠ 1)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (h1 : h * x * h⁻¹ = x ^ 3 * y ^ 0 * ⁅x, y⁆ ^ 3) (h3 : h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 4) :
    OddLocalWitness S := by
  have hz5 : ⁅x, y⁆ ^ 5 = 1 := by
    rw [← orderOf_commutator_of_cubic Nat.prime_five hx hz hzx]
    exact pow_orderOf_eq_one _
  have hxz : Commute x ⁅x, y⁆ := hzx.symm
  simp only [pow_zero, mul_one] at h1
  have hcx : MulAut.conj h x = x ^ 3 * ⁅x, y⁆ ^ 3 := by rw [MulAut.conj_apply, h1]
  have hcz : MulAut.conj h ⁅x, y⁆ = x ^ 0 * ⁅x, y⁆ ^ 4 := by
    rw [MulAut.conj_apply, h3, pow_zero, one_mul]
  have hc2x : MulAut.conj (h ^ 2) x = x ^ 4 * ⁅x, y⁆ ^ 1 := by
    rw [conj_sq_apply, hcx, conj_mono hxz hx hz5 _ hcx hcz]
  have hc2z : MulAut.conj (h ^ 2) ⁅x, y⁆ = x ^ 0 * ⁅x, y⁆ ^ 1 := by
    rw [conj_sq_apply, hcz, conj_mono hxz hx hz5 _ hcx hcz]
  have h2z : Commute (h ^ 2) ⁅x, y⁆ :=
    commute_iff_conj_eq.2 (by rw [hc2z, pow_zero, one_mul, pow_one])
  have h4 : Commute ((h ^ 2) ^ 2 ^ 1) x := by
    rw [commute_iff_conj_eq, pow_one, conj_sq_apply, hc2x, conj_mono hxz hx hz5 _ hc2x hc2z]
    norm_num
  have hn : ¬ Commute (h ^ 2) x := fun hc => hz (by
    rw [commute_iff_conj_eq, hc2x, pow_one] at hc
    have e : ⁅x, y⁆ = (x ^ 4)⁻¹ * x := eq_inv_mul_iff_mul_eq.2 hc
    rw [inv_eq_of_mul_eq_one_right (show x ^ 4 * x = 1 by rw [← pow_succ]; exact hx),
      ← pow_two] at e
    exact commutator_eq_one_of_commute_pow (k := 2) (j := 3) hx (by norm_num) (e ▸ hzy))
  exact ⟨5, Nat.prime_five, by norm_num, two_le_pRank_of_cubic Nat.prime_five hx hz hzx hzy,
    one_le_localRank_of_commute_even (by norm_num) h2z
      (orderOf_commutator_of_cubic Nat.prime_five hx hz hzx) (even_orderOf_of_commute_pow 1 h4 hn)⟩

theorem oddLocalWitness_of_square_Tits (hx : x ^ 5 = 1) (hy : y ^ 5 = 1) (hxy : x * y = y * x)
    (hc : Nat.card (Subgroup.closure ({x, y} : Set S)) = 5 ^ 2)
    (h1 : h * x * h⁻¹ = x ^ 3 * y ^ 3) (h2 : h * y * h⁻¹ = x ^ 4 * y ^ 2) :
    OddLocalWitness S := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hxy' : Commute x y := hxy
  have hcx : MulAut.conj h x = x ^ 3 * y ^ 3 := by rw [MulAut.conj_apply, h1]
  have hcy : MulAut.conj h y = x ^ 4 * y ^ 2 := by rw [MulAut.conj_apply, h2]
  have hnot : ∀ n : ℕ, y = x ^ n → False := fun n hn => by
    have hle := card_closure_pair_le (x := y) (by norm_num) hx n hn
    rw [Set.pair_comm] at hle
    exact (by norm_num : ¬ (5 ^ 2 : ℕ) ≤ 5) (hc ▸ hle)
  have hw : Commute h (x ^ 3 * y ^ 1) := commute_iff_conj_eq.2 (by
    rw [conj_mono hxy' hx hy _ hcx hcy])
  have hw1 : x ^ 3 * y ^ 1 ≠ 1 := fun h0 => hnot 2 (by
    rw [pow_one] at h0
    rw [eq_inv_of_mul_eq_one_right h0]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact hx))
  have hw5 : (x ^ 3 * y ^ 1) ^ 5 = 1 := by
    rw [(hxy'.pow_pow 3 1).mul_pow, ← pow_mul, ← pow_mul, pow_eq_pow_mod _ hx,
      pow_eq_pow_mod _ hy]
    norm_num
  have hsq : Commute (h ^ 2 ^ 1) y := by
    rw [commute_iff_conj_eq, pow_one, conj_sq_apply, hcy, conj_mono hxy' hx hy _ hcx hcy]
    norm_num
  have hn : ¬ Commute h y := fun hc' => by
    rw [commute_iff_conj_eq, hcy] at hc'
    have h3 : x ^ 4 * y = 1 := by
      have e : x ^ 4 * y * y = 1 * y := by rw [one_mul, mul_assoc, ← pow_two]; exact hc'
      exact mul_right_cancel e
    refine hnot 1 ?_
    rw [eq_inv_of_mul_eq_one_right h3, pow_one]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact hx)
  exact ⟨5, Nat.prime_five, by norm_num, two_le_pRank_of_square Nat.prime_five hx hy hxy hc,
    one_le_localRank_of_commute_even (by norm_num) hw (orderOf_eq_prime hw5 hw1)
      (even_orderOf_of_commute_pow 1 hsq hn)⟩

end CFSG.SectionRank.QTK
