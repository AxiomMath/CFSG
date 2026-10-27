module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.GH74.Uniqueness

theorem arith_172b {q Q r W c A B : ℕ} (hq : 2 ≤ q) (hqQ : q ∣ Q) (hQ : 0 < Q) (hW : 0 < W)
    (hA : A = (q - 1) * W) (hB : B = c * W) (h171 : (r - (Q + 1)) * B = Q * (Q + 1) * A)
    (hr : Q + 1 ≤ r) (hdiv : q * Q ∣ r - 1) : c ≡ 1 [MOD q] := by
  obtain ⟨m, hm⟩ := hdiv
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hm
      omega
    · exact h0
  have hqm : 1 ≤ q * m := Nat.mul_pos (by omega) hm1
  have h1 : r - (Q + 1) = Q * (q * m - 1) := by
    have e : q * Q * m = Q * (q * m) := by ring
    rw [Nat.mul_sub, mul_one]
    omega
  have h2 : (q * m - 1) * c = (Q + 1) * (q - 1) := by
    have h3 : (Q * W) * ((q * m - 1) * c) = (Q * W) * ((Q + 1) * (q - 1)) := by
      calc (Q * W) * ((q * m - 1) * c) = (Q * (q * m - 1)) * (c * W) := by ring
        _ = (r - (Q + 1)) * B := by rw [h1, hB]
        _ = Q * (Q + 1) * A := h171
        _ = (Q * W) * ((Q + 1) * (q - 1)) := by rw [hA]; ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hQ hW) h3
  have h4 : q * m * c = (Q + 1) * (q - 1) + c := by
    have : (q * m - 1) * c + c = q * m * c := by
      calc (q * m - 1) * c + c = (q * m - 1 + 1) * c := by ring
        _ = q * m * c := by rw [Nat.sub_add_cancel hqm]
    omega
  have h5 : q ∣ (q - 1) + c := by
    have h6 : q ∣ (Q + 1) * (q - 1) + c := ⟨m * c, by rw [← h4]; ring⟩
    have h7 : (Q + 1) * (q - 1) + c = Q * (q - 1) + ((q - 1) + c) := by ring
    rw [h7] at h6
    exact (Nat.dvd_add_right (Dvd.dvd.mul_right hqQ _)).mp h6
  have h8 : q ∣ 1 + (q - 1) := by
    have : 1 + (q - 1) = q := by omega
    rw [this]
  have h9 : (c + (q - 1)) ≡ (1 + (q - 1)) [MOD q] := by
    rw [add_comm c (q - 1)]
    exact (Nat.modEq_zero_iff_dvd.mpr h5).trans (Nat.modEq_zero_iff_dvd.mpr h8).symm
  exact Nat.ModEq.add_right_cancel' (q - 1) h9

end CFSG.GH74.Uniqueness
