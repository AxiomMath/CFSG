module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFive
public import CFSG.Adapters.StatedClassicalOrders
public import CFSG.Mathlib.Arithmetic.TwoPowModThree
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.Quasithin.E1 CFSG.LocalAnalysis.RankThreeUC.AGL81C
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem statedClassicalModel_psl_three_of_mulEquiv {X : Type} [Group X] {n : ℕ}
    (hn : n ≠ 0) (e : X ≃* PSL(3, GaloisField 2 n)) :
    StatedClassicalModel X .PSL 3 2 n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨⟨Nat.prime_two, Nat.one_le_iff_ne_zero.mpr hn, by norm_num, ?_, ?_⟩,
    GaloisField 2 n, inferInstance, inferInstance, GaloisField.card 2 n hn,
    ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 _)⟩⟩
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega

theorem gcd_three_two_pow_sub_one_of_odd {n : ℕ} (hn : Odd n) :
    Nat.gcd 3 (2 ^ n - 1) = 1 := by
  have hmod : 2 ^ n % 3 = 2 := CFSG.two_pow_mod_three_of_odd hn
  have hnot : ¬ 3 ∣ 2 ^ n - 1 := by
    intro h
    obtain ⟨k, hk⟩ := h
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2n : 2 ^ n = 3 * k + 1 := (Nat.sub_eq_iff_eq_add hpos).mp hk
    rw [h2n, Nat.mul_add_mod_self_left] at hmod
    norm_num at hmod
  have hcop : Nat.Coprime 3 (2 ^ n - 1) :=
    (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).mpr hnot
  rwa [Nat.coprime_iff_gcd_eq_one] at hcop

theorem card_of_isL3TwoPow_of_odd {X : Type} [Group X] {n : ℕ} (hn : Odd n)
    (hX : IsL3TwoPow n X) :
    Nat.card X = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  unfold IsL3TwoPow IsPSLType at hX
  obtain ⟨e⟩ := hX
  have hcard := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (X := X)
    (k := 3) (p := 2) (e := n) (by norm_num)
    (statedClassicalModel_psl_three_of_mulEquiv hn0 e)
  rw [gcd_three_two_pow_sub_one_of_odd hn, Nat.div_one] at hcard
  simpa [Finset.prod_Icc_succ_top (by norm_num : 1 + 1 ≤ 3), Nat.mul_assoc] using hcard

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
