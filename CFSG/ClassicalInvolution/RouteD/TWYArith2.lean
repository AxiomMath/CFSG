module

public import CFSG.ClassicalInvolution.RouteD.TWYArith

public section

namespace CFSG.ClassicalInvolution.RouteD.TWY

open CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.RouteD.NonClassical

variable {p f q : ℕ}

theorem framesPlus_ne_zero (hq : 2 ≤ q) (j : ℕ) : framesPlus q j ≠ 0 := by
  unfold framesPlus
  have hpos : 0 < q := by omega
  exact Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (pow_sub_one_ne_zero' hq (by omega))
    (by omega)) (pow_pos hpos _).ne') (Nat.mul_ne_zero (Nat.mul_ne_zero
    (pow_sub_one_ne_zero' hq (by omega)) (by omega)) (pow_pos hpos _).ne')

theorem framesMinus_ne_zero (hq : 2 ≤ q) (j : ℕ) : framesMinus q j ≠ 0 := by
  unfold framesMinus
  have hpos : 0 < q := by omega
  exact Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (by omega)
    (pow_sub_one_ne_zero' hq (by omega))) (pow_pos hpos _).ne') (Nat.mul_ne_zero
    (Nat.mul_ne_zero (by omega) (pow_sub_one_ne_zero' hq (by omega))) (pow_pos hpos _).ne')

theorem framesMinus_lt_framesPlus_succ (hq : 2 ≤ q) (j : ℕ) :
    framesMinus q j < framesPlus q (j + 1) := by
  unfold framesPlus framesMinus
  have hCA : q ^ (j + 1) < q ^ (j + 1 + 1 + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  have hC : 2 ≤ q ^ (j + 1) := by
    calc 2 ≤ q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hB : 2 ≤ q ^ (j + 1 + 1) := by
    calc 2 ≤ q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ (j + 1 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have e1 : q ^ (2 * (j + 1 + 1)) = (q ^ (j + 1 + 1)) ^ 2 := pow_mul' q 2 _
  have e2 : q ^ (2 * (j + 1)) = (q ^ (j + 1)) ^ 2 := pow_mul' q 2 _
  rw [e1, e2]
  generalize q ^ (j + 1 + 1 + 1) = A at hCA ⊢
  generalize q ^ (j + 1 + 1) = B at hB ⊢
  generalize q ^ (j + 1) = C at hCA hC ⊢
  obtain ⟨a, rfl⟩ : ∃ a, A = a + 1 := ⟨A - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, B = b + 1 := ⟨B - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, C = c + 1 := ⟨C - 1, by omega⟩
  have hb : 1 ≤ b := by omega
  have hca : c < a := by omega
  have hK : 0 < b * (b + 2) * (b + 1) ^ 2 * (c + 1) ^ 2 := by positivity
  have hin : (a + 2) * c < a * (c + 2) := by nlinarith
  simp only [Nat.add_sub_cancel]
  calc ((a + 1 + 1) * b * (b + 1) ^ 2) * (((b + 1 + 1) * c) * (c + 1) ^ 2)
      = (b * (b + 2) * (b + 1) ^ 2 * (c + 1) ^ 2) * ((a + 2) * c) := by ring
    _ < (b * (b + 2) * (b + 1) ^ 2 * (c + 1) ^ 2) * (a * (c + 2)) :=
        Nat.mul_lt_mul_of_pos_left hin hK
    _ = ((a * (b + 1 + 1)) * (b + 1) ^ 2) * ((b * (c + 1 + 1)) * (c + 1) ^ 2) := by ring

theorem framesPlus_ne_framesMinus (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hqdef : q = p ^ f)
    (hq5 : 5 ≤ q) (j j' : ℕ) : framesPlus q j ≠ framesMinus q j' := by
  intro h
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  have h' := h
  rw [framesPlus_eq hqdef, framesMinus_eq hqdef] at h'
  have hx := pow_eq_of_mul_eq hp (framesPlus_unit hp hp2 hpq hq1 j)
    (framesMinus_unit hp hp2 hpq hq1 j') h'
  have h3 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
  obtain rfl : j = j' + 1 := by omega
  exact absurd h (Nat.ne_of_gt (framesMinus_lt_framesPlus_succ (by omega) j'))

end CFSG.ClassicalInvolution.RouteD.TWY
