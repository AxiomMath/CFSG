module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2EvenOuter
public import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarBound
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2Small

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.GH74.Uniqueness.Bender
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (higher_linear_outer_order_divides_field_gcd_bound)

theorem two_pow_three_mul_two_mul_lt (n : ℕ) : 2 ^ (n * 3) * (2 * n) < 2 * (2 ^ n) ^ 4 := by
  have h1 : n < 2 ^ n := Nat.lt_two_pow_self
  have h2 : 0 < 2 ^ (n * 3) := by positivity
  calc 2 ^ (n * 3) * (2 * n) < 2 ^ (n * 3) * (2 * 2 ^ n) :=
        Nat.mul_lt_mul_of_pos_left (by omega) h2
    _ = 2 * (2 ^ n) ^ 4 := by ring

theorem odd_gcd_three (m : ℕ) : Odd (Nat.gcd 3 m) := by
  have h := Nat.gcd_dvd_left 3 m
  have h3 : Nat.gcd 3 m = 1 ∨ Nat.gcd 3 m = 3 := (Nat.dvd_prime Nat.prime_three).mp h
  rcases h3 with h3 | h3 <;> rw [h3] <;> decide

theorem card_lt_of_isPGroup_mulAut_psl2_sq {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 1 ≤ n)
    (h : LieModel X .PSL 2 2 (2 * n)) {P : Subgroup (MulAut X)} (hP : IsPGroup 2 P) :
    Nat.card P < 2 * (2 ^ n) ^ 4 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_psl2Model_of_lieModel h
  have h1 := card_le_of_isPGroup_mulAut_psl2 (by omega : 2 ≤ 2 * n) e hP
  have h2 := two_pow_padicValNat_lt (f := 2 * n) (by omega)
  have h3 : 0 < 2 ^ (2 * n) := by positivity
  calc Nat.card P ≤ 2 ^ (2 * n) * 2 ^ padicValNat 2 (2 * n) := h1
    _ < 2 ^ (2 * n) * 2 ^ (2 * n) := Nat.mul_lt_mul_of_pos_left h2 h3
    _ = (2 ^ n) ^ 4 := by ring
    _ < 2 * (2 ^ n) ^ 4 := by
        have : 0 < (2 ^ n) ^ 4 := by positivity
        omega

theorem card_lt_of_isPGroup_mulAut_psu3 {X : Type} [Group X] [Finite X] (hs : IsSimpleGroup X)
    (hna : ∃ a b : X, a * b ≠ b * a) {n : ℕ} (hn : 2 ≤ n) (h : LieModel X .PSU 3 2 n)
    {P : Subgroup (MulAut X)} (hP : IsPGroup 2 P) : Nat.card P < 2 * (2 ^ n) ^ 4 := by
  obtain ⟨e, hB⟩ := exists_benderType_of_lieModel_psu3 hn h
  obtain ⟨Dd, _, -, hDd, -, hQ⟩ := hB.outer_unitary
  have hout : Nat.card (Outer X) = Nat.gcd 3 (2 ^ n + 1) * (2 * n) := by
    rw [← hDd, ← hQ, mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup Dd
  have hZ : center X = ⊥ := center_eq_bot_of_simple_nonabelian hs hna
  have hcardX : Nat.card X = Open.ordTwistedA 2 (2 ^ n) :=
    F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) h
  obtain ⟨r, hr, hrX⟩ := (Timmesfeld.Orders.profile_ordTwistedA (n := 2) le_rfl
    (by omega : 1 ≤ n)).two
  have : Finite (MulAut X) :=
    Finite.of_injective (fun β : MulAut X => (β : X → X)) DFunLike.coe_injective
  refine lt_of_le_of_lt (card_le_of_isPGroup_of_card_dvd hP (N := 2 ^ (n * 3) * (2 * n))
    (u := r * Nat.gcd 3 (2 ^ n + 1)) (hr.mul (odd_gcd_three _)) (by positivity) ?_)
    (two_pow_three_mul_two_mul_lt n)
  rw [card_mulAut_of_center_eq_bot hZ, hcardX, hrX, hout]
  exact dvd_of_eq (by ring)

theorem card_lt_of_isPGroup_mulAut_psl3 {X : Type} [Group X] [Finite X] (hs : IsSimpleGroup X)
    (hna : ∃ a b : X, a * b ≠ b * a) {n : ℕ} (hn : 1 ≤ n) (h : LieModel X .PSL 3 2 n)
    {P : Subgroup (MulAut X)} (hP : IsPGroup 2 P) : Nat.card P < 2 * (2 ^ n) ^ 4 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearPilot.exists_projectiveSL_equiv_of_lieModel_PSL h
  have hout : Nat.card (Outer X) ∣ 2 * n * Nat.gcd 3 (2 ^ n - 1) := by
    rw [Nat.card_congr (OuterAutomorphisms.equivalence e).toEquiv]
    exact higher_linear_outer_order_divides_field_gcd_bound Nat.prime_two hn le_rfl hK
  have hZ : center X = ⊥ := center_eq_bot_of_simple_nonabelian hs hna
  have hcardX : Nat.card X = Open.ordA 2 (2 ^ n) := LinearPilot.card_of_lieModel_PSL_two h
  obtain ⟨r, hr, hrX⟩ := (Timmesfeld.Orders.profile_ordA (n := 2) (by norm_num) hn).two
  have : Finite (MulAut X) :=
    Finite.of_injective (fun β : MulAut X => (β : X → X)) DFunLike.coe_injective
  refine lt_of_le_of_lt (card_le_of_isPGroup_of_card_dvd hP (N := 2 ^ (n * 3) * (2 * n))
    (u := r * Nat.gcd 3 (2 ^ n - 1)) (hr.mul (odd_gcd_three _)) (by positivity) ?_)
    (two_pow_three_mul_two_mul_lt n)
  rw [card_mulAut_of_center_eq_bot hZ, hcardX, hrX]
  obtain ⟨c, hc⟩ := hout
  refine ⟨c, ?_⟩
  have e3 : n * (2 * (2 + 1) / 2) = n * 3 := by norm_num
  rw [e3]
  calc 2 ^ (n * 3) * (2 * n) * (r * Nat.gcd 3 (2 ^ n - 1)) =
        2 ^ (n * 3) * r * (2 * n * Nat.gcd 3 (2 ^ n - 1)) := by ring
    _ = 2 ^ (n * 3) * r * (Nat.card (Outer X) * c) := by rw [hc]
    _ = 2 ^ (n * 3) * r * Nat.card (Outer X) * c := by ring

theorem catSL2EvenOuterBound_of_list {n : ℕ} (hlist : CatSL2EvenOuterList n) :
    CatSL2EvenOuterBound n := by
  intro J _ _ hJ hna heven τ hout hyp P hP
  have hn : 2 ≤ n := by
    obtain ⟨-, D, -, hDm, -⟩ := hyp
    exact two_le_of_lieModel_PSL_two_two hDm
  rcases hlist J hJ hna heven τ hout hyp with h | h | h
  · exact card_lt_of_isPGroup_mulAut_psl2_sq (by omega) h hP
  · exact card_lt_of_isPGroup_mulAut_psu3 hJ hna hn h hP
  · exact card_lt_of_isPGroup_mulAut_psl3 hJ hna (by omega) h hP

section Bound


theorem catSL2EvenOuterBound (n : ℕ) : CatSL2EvenOuterBound n :=
  catSL2EvenOuterBound_of_list (catSL2EvenOuterList n)

end Bound

end CFSG.SeitzReduction.RankOne
