module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10ADef
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzR10A

private lemma fzrAux_num_eq {n : ℕ} (hn : n < 64) : n % 8 + 8 * (n / 8 % 8) = n := by
  have h : n / 8 % 8 = n / 8 := Nat.mod_eq_of_lt (by omega)
  rw [h, Nat.mod_add_div]

theorem fzr_a_ap_lt (m : Mat) (n : ℕ) : m.ap n < 64 := by
  rw [Mat.ap]
  omega

theorem fzr_a_mul_lt (m n : Mat) : FzR10AMatLt (m.mul n) := by
  rw [FzR10AMatLt, Mat.mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> exact Nat.mod_lt _ (by omega)

theorem fzr_a_ap_one {n : ℕ} (hn : n < 64) : Mat.one.ap n = n := by
  rw [Mat.ap, Mat.one]
  simp only [Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add, Nat.mod_mod]
  exact fzrAux_num_eq hn

theorem fzr_a_addP_lt (p q : ℕ) : addP p q < 64 := by
  rw [addP]
  omega

theorem fzr_a_subP_lt (p q : ℕ) : subP p q < 64 := by
  rw [subP]
  have h : p % 8 + 8 - q % 8 = p % 8 + (8 - q % 8) := by omega
  rw [h]
  omega

end CFSG.OddStandard.SmallF3.FritzII
