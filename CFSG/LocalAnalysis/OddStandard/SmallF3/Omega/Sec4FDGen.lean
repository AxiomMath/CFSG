module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrCover

public section

namespace CFSG.OddStandard.SmallF3.Omega

private lemma sec4FD_conj_pow_inv {H : Type} [Group H] {a b : H} (ha : a * a = 1)
    (hb : b * b = 1) (j : ℕ) : a * (a * b) ^ j * a = ((a * b) ^ j)⁻¹ := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hc : (a * b)⁻¹ = b * a := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]
  have h1 : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [hai]
    have haa : a * (a * b) * a = b * a := by
      calc a * (a * b) * a = (a * a) * (b * a) := by group
        _ = b * a := by rw [ha, one_mul]
    rw [haa, hc]
  have h2 : (a * (a * b) * a⁻¹) ^ j = a * (a * b) ^ j * a⁻¹ := conj_pow
  rw [h1, hai, inv_pow] at h2
  exact h2.symm

theorem sec4FD_exists_pow_conj {H : Type} [Group H] {a b : H} (ha : a * a = 1) (hb : b * b = 1)
    (hodd : Odd (orderOf (a * b))) :
    ∃ k : ℕ, b = (a * b) ^ k * a * ((a * b) ^ k)⁻¹ := by
  obtain ⟨m, hm⟩ := hodd
  have h1 : a * (a * b) ^ m * a = ((a * b) ^ m)⁻¹ := sec4FD_conj_pow_inv ha hb m
  have h2 : a * ((a * b) ^ m)⁻¹ = (a * b) ^ m * a := by
    calc a * ((a * b) ^ m)⁻¹ = a * (a * (a * b) ^ m * a) := by rw [h1]
      _ = a * a * (a * b) ^ m * a := by group
      _ = (a * b) ^ m * a := by rw [ha, one_mul]
  have hc : (a * b)⁻¹ = b * a := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]
  have h2m : (a * b) ^ (2 * m) = (a * b)⁻¹ := by
    have hord : (a * b) ^ (2 * m) * (a * b) = 1 := by
      rw [← pow_succ, ← hm]; exact pow_orderOf_eq_one _
    exact (mul_eq_one_iff_eq_inv).mp hord
  refine ⟨m, ?_⟩
  have hmain : (a * b) ^ m * a * ((a * b) ^ m)⁻¹ = b := by
    calc (a * b) ^ m * a * ((a * b) ^ m)⁻¹
        = (a * b) ^ m * (a * ((a * b) ^ m)⁻¹) := mul_assoc _ _ _
      _ = (a * b) ^ m * ((a * b) ^ m * a) := by rw [h2]
      _ = (a * b) ^ m * (a * b) ^ m * a := (mul_assoc _ _ _).symm
      _ = (a * b) ^ (m + m) * a := by rw [pow_add]
      _ = (a * b) ^ (2 * m) * a := by rw [show m + m = 2 * m by omega]
      _ = (a * b)⁻¹ * a := by rw [h2m]
      _ = b := by rw [hc, mul_assoc, ha, mul_one]
  exact hmain.symm

theorem sec4FD_natCard_quotient_center_dvd {K C : Type} [Group K] [Group C] [Finite K] [Finite C]
    (f : K →* C) (hf : f.ker ≤ Subgroup.center K) :
    Nat.card (K ⧸ Subgroup.center K) ∣ Nat.card C := by
  calc Nat.card (K ⧸ Subgroup.center K) = (Subgroup.center K).index := rfl
    _ ∣ f.ker.index := Subgroup.index_dvd_of_le hf
    _ = Nat.card f.range := Subgroup.index_ker f
    _ ∣ Nat.card C := Subgroup.card_subgroup_dvd_card f.range

end CFSG.OddStandard.SmallF3.Omega
