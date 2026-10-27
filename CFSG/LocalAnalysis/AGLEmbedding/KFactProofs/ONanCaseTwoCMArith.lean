module

public import CFSG.Open.Defs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem dvd_mul_div_of_dvd {a b g : ℕ} (h : g ∣ b) : a ∣ a * b / g := by
  rw [Nat.mul_div_assoc a h]
  exact dvd_mul_right _ _

theorem sub_one_dvd_pow_sub_one (q i : ℕ) : q - 1 ∣ q ^ i - 1 := by
  simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow q 1 i

theorem pow_dvd_ordA (n q : ℕ) (hn : 1 ≤ n) : q ^ (n * (n + 1) / 2) ∣ ordA n q := by
  unfold ordA
  refine dvd_mul_div_of_dvd ?_
  refine (Nat.gcd_dvd_right _ _).trans ?_
  refine (sub_one_dvd_pow_sub_one q 2).trans ?_
  exact Finset.dvd_prod_of_mem (fun i => q ^ i - 1) (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)

theorem pow_dvd_ordTwistedA (n q : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q) :
    q ^ (n * (n + 1) / 2) ∣ ordTwistedA n q := by
  unfold ordTwistedA
  refine dvd_mul_div_of_dvd ?_
  refine (Nat.gcd_dvd_right _ _).trans ?_
  have h2 : (q ^ 2 - (-1 : ℤ) ^ 2).toNat = q ^ 2 - 1 := by
    have : (q : ℤ) ^ 2 - (-1) ^ 2 = ((q ^ 2 - 1 : ℕ) : ℤ) := by
      have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
      push_cast [Nat.cast_sub this]
      ring
    rw [this, Int.toNat_natCast]
  have hd : q + 1 ∣ q ^ 2 - 1 := by
    refine ⟨q - 1, ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have : (k + 1) ^ 2 = (k + 1 + 1) * k + 1 := by ring
    rw [this, Nat.add_sub_cancel]
  refine hd.trans ?_
  rw [← h2]
  exact Finset.dvd_prod_of_mem (fun i => (((q : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i).toNat)
    (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)

theorem pow_dvd_ordBC (n q : ℕ) (hn : 1 ≤ n) : q ^ (n * n) ∣ ordBC n q := by
  unfold ordBC
  refine dvd_mul_div_of_dvd ?_
  refine (Nat.gcd_dvd_right _ _).trans ?_
  refine (sub_one_dvd_pow_sub_one q (2 * 1)).trans ?_
  exact Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)

theorem pow_dvd_ordD (n q : ℕ) : q ^ (n * (n - 1)) ∣ ordD n q := by
  unfold ordD
  rw [mul_assoc]
  refine dvd_mul_div_of_dvd ?_
  exact (Nat.gcd_dvd_right _ _).trans (dvd_mul_right _ _)

theorem pow_dvd_ordTwistedD (n q : ℕ) : q ^ (n * (n - 1)) ∣ ordTwistedD n q := by
  unfold ordTwistedD
  rw [mul_assoc]
  refine dvd_mul_div_of_dvd ?_
  exact (Nat.gcd_dvd_right _ _).trans (dvd_mul_right _ _)

theorem pow_dvd_ordG2 (q : ℕ) : q ^ 6 ∣ ordG2 q := by
  unfold ordG2
  exact ⟨(q ^ 6 - 1) * (q ^ 2 - 1), mul_assoc _ _ _⟩

end CFSG.AGLEmbedding
