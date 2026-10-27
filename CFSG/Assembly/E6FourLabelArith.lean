module

public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Assembly

theorem e6Four_two_pow_mod_five (n : ℕ) : 2 ^ n % 5 = 2 ^ (n % 4) % 5 := by
  conv_lhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem e6Four_five_dvd_two_pow_sub_one {n : ℕ} : 5 ∣ 2 ^ n - 1 ↔ 4 ∣ n := by
  have h := e6Four_two_pow_mod_five n
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with hr | hr | hr | hr <;>
    rw [hr] at h <;> norm_num at h <;> omega

theorem e6Four_five_dvd_two_pow_add_one {n : ℕ} : 5 ∣ 2 ^ n + 1 ↔ n % 4 = 2 := by
  have h := e6Four_two_pow_mod_five n
  rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with hr | hr | hr | hr <;>
    rw [hr] at h <;> norm_num at h <;> omega

end CFSG.Assembly

end
