module

public import CFSG.Open.Defs
import CFSG.Timmesfeld.Orders.ClassicalUnitaryThree
import CFSG.Timmesfeld.Orders.ClassicalLinearThree
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MFMuZ2

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.ClassicalOrders

theorem z32_l3 : ∀ r : ZMod 32, r.val % 4 = 1 → (r ^ 2 - 1) * (r ^ 3 - 1) = 0 := by decide

theorem z16_l3 : ∀ r : ZMod 16, r.val % 4 = 3 → (r ^ 2 - 1) * (r ^ 3 - 1) = 0 := by decide

theorem z16_u3 : ∀ r : ZMod 16, r.val % 4 = 1 → (r ^ 2 - 1) * (r ^ 3 + 1) = 0 := by decide

theorem z32_u3 : ∀ r : ZMod 32, r.val % 4 = 3 → (r ^ 2 - 1) * (r ^ 3 + 1) = 0 := by decide

theorem z32_odd : ∀ r : ZMod 32, r.val % 2 = 1 → (r ^ 6 - 1) * (r ^ 2 - 1) = 0 := by decide

theorem val_natCast_mod {n m : ℕ} [NeZero n] (hmn : m ∣ n) (q : ℕ) :
    (q : ZMod n).val % m = q % m := by
  rw [ZMod.val_natCast, Nat.mod_mod_of_dvd q hmn]

theorem cast_sub_mul {n q a b : ℕ} (hq : 1 ≤ q) :
    (((q ^ a - 1) * (q ^ b - 1) : ℕ) : ZMod n) = ((q : ZMod n) ^ a - 1) * ((q : ZMod n) ^ b - 1) ∧
      (((q ^ a - 1) * (q ^ b + 1) : ℕ) : ZMod n) =
        ((q : ZMod n) ^ a - 1) * ((q : ZMod n) ^ b + 1) := by
  have ha := Nat.one_le_pow a q hq
  have hb := Nat.one_le_pow b q hq
  refine ⟨?_, ?_⟩ <;> push_cast [Nat.cast_sub ha, Nat.cast_sub hb] <;> ring

theorem dvd_of_mul_gcd {a b c m : ℕ} (hm : Nat.Coprime m 3) (h : a * Nat.gcd 3 c = b)
    (hb : m ∣ b) : m ∣ a :=
  (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 c) hm).dvd_of_dvd_mul_right (h ▸ hb)

theorem card_psl3_mul (K : Type) [Field K] [Finite K] :
    Nat.card (StatedProj (StatedSL 3 K)) * Nat.gcd 3 (Nat.card K - 1) =
      Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) :=
  CFSG.Timmesfeld.ClassicalOrders.card_psl_three_mul_gcd (K := K)

theorem thirtyTwo_dvd_psl3_of_one {K : Type} [Field K] [Finite K] (hq : Nat.card K % 4 = 1) :
    32 ∣ Nat.card (StatedProj (StatedSL 3 K)) := by
  have h : 32 ∣ (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) := by
    rw [← ZMod.natCast_eq_zero_iff, (cast_sub_mul (q := Nat.card K) (by omega)).1]
    exact z32_l3 _ (by rw [val_natCast_mod (by norm_num)]; exact hq)
  exact dvd_of_mul_gcd (by norm_num) (card_psl3_mul K) (h.mul_left _)

theorem sixteen_dvd_psl3_of_three {K : Type} [Field K] [Finite K] (hq : Nat.card K % 4 = 3) :
    16 ∣ Nat.card (StatedProj (StatedSL 3 K)) := by
  have h : 16 ∣ (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) := by
    rw [← ZMod.natCast_eq_zero_iff, (cast_sub_mul (q := Nat.card K) (by omega)).1]
    exact z16_l3 _ (by rw [val_natCast_mod (by norm_num)]; exact hq)
  exact dvd_of_mul_gcd (by norm_num) (card_psl3_mul K) (h.mul_left _)

theorem thirtyTwo_dvd_psl3_of_two {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) : 32 ∣ Nat.card (StatedProj (StatedSL 3 K)) := by
  have h : 32 ∣ Nat.card K ^ 3 := by
    rw [hK, ← pow_mul]
    exact (Nat.pow_dvd_pow 2 (by omega : 5 ≤ f * 3))
  exact dvd_of_mul_gcd (by norm_num) (card_psl3_mul K) (h.mul_right _)

theorem card_psu3_mul {K : Type} [Field K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) :
    Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) * Nat.gcd 3 (p ^ f + 1) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) :=
  CFSG.Timmesfeld.ClassicalOrders.card_psu_three_mul_gcd hp hf hK

theorem thirtyTwo_dvd_psu3_of_three {K : Type} [Field K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 3) :
    32 ∣ Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) := by
  have h : 32 ∣ ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
    rw [← ZMod.natCast_eq_zero_iff, (cast_sub_mul (q := p ^ f) (by omega)).2]
    exact z32_u3 _ (by rw [val_natCast_mod (by norm_num)]; exact hq)
  exact dvd_of_mul_gcd (by norm_num) (card_psu3_mul hp hf hK) (h.mul_left _)

theorem sixteen_dvd_psu3_of_one {K : Type} [Field K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1) :
    16 ∣ Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) := by
  have h : 16 ∣ ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
    rw [← ZMod.natCast_eq_zero_iff, (cast_sub_mul (q := p ^ f) (by omega)).2]
    exact z16_u3 _ (by rw [val_natCast_mod (by norm_num)]; exact hq)
  exact dvd_of_mul_gcd (by norm_num) (card_psu3_mul hp hf hK) (h.mul_left _)

theorem thirtyTwo_dvd_psu3_of_two {K : Type} [Field K] {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) : 32 ∣ Nat.card (StatedProj (StatedSU 3 (2 ^ f) K)) := by
  have h : 32 ∣ (2 ^ f) ^ 3 := by
    rw [← pow_mul]
    exact (Nat.pow_dvd_pow 2 (by omega : 5 ≤ f * 3))
  exact dvd_of_mul_gcd (by norm_num) (card_psu3_mul Nat.prime_two (by omega) hK) (h.mul_right _)

theorem thirtyTwo_dvd_ordG2_of_odd {q : ℕ} (hq : q % 2 = 1) : 32 ∣ ordG2 q := by
  rw [ordG2, mul_assoc]
  refine Dvd.dvd.mul_left ?_ _
  rw [← ZMod.natCast_eq_zero_iff, (cast_sub_mul (q := q) (by omega)).1]
  exact z32_odd _ (by rw [val_natCast_mod (by norm_num)]; exact hq)

theorem thirtyTwo_dvd_ordG2_two {f : ℕ} (hf : 1 ≤ f) : 32 ∣ ordG2 (2 ^ f) := by
  rw [ordG2, mul_assoc]
  refine Dvd.dvd.mul_right ?_ _
  rw [← pow_mul]
  exact (Nat.pow_dvd_pow 2 (by omega : 5 ≤ f * 6))

theorem thirtyTwo_dvd_ordTrialityD4_of_odd {q : ℕ} (hq : q % 2 = 1) :
    32 ∣ ordTrialityD4 q := by
  rw [ordTrialityD4, mul_assoc]
  refine Dvd.dvd.mul_left ?_ _
  rw [← ZMod.natCast_eq_zero_iff, (cast_sub_mul (q := q) (by omega)).1]
  exact z32_odd _ (by rw [val_natCast_mod (by norm_num)]; exact hq)

theorem thirtyTwo_dvd_ordTrialityD4_two {f : ℕ} (hf : 1 ≤ f) : 32 ∣ ordTrialityD4 (2 ^ f) := by
  rw [ordTrialityD4, mul_assoc, mul_assoc]
  refine Dvd.dvd.mul_right ?_ _
  rw [← pow_mul]
  exact (Nat.pow_dvd_pow 2 (by omega : 5 ≤ f * 12))

end CFSG.ClassicalInvolution.Q3.TL4.MFMuZ2
