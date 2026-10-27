module

public import CFSG.GH74.GLS.LU.Local.L3Cover
public import CFSG.RankThree.PartOne.LIT.RankMatrix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.OddCoversLift
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin.B69K.OddCovers

open CFSG.Open Matrix CFSG.RankThree.PerfectCover
open scoped MatrixGroups

theorem pRank_three_le_two_specialLinear_three {K : Type} [Field K] [Finite K] [CharP K 2] :
    CFSG.Open.pRank 3 (⊤ : Subgroup SL(3, K)) ≤ 2 := by
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K)]
  exact CFSG.RankThree.PartOne.LIT.pRank_le_two_of_det_gl Nat.prime_three
    (CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo Nat.prime_three (by norm_num))
    (by simp) (CFSG.Open.StatedSL 3 K) (fun h hh => CFSG.Open.StatedAPI.det_of_mem_statedSL hh)

theorem card_center_specialLinear_three {K : Type} [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    Nat.card (Subgroup.center SL(3, K)) = 3 := by
  rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center K 3 (by norm_num)]
  exact Nat.gcd_eq_left h3

theorem pRank_three_le_two_statedSU_three {K : Type} [Field K] [Finite K] [CharP K 2] {q : ℕ} :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSU 3 q K)) ≤ 2 := by
  have hK3 : ((3 : ℕ) : K) ≠ 0 :=
    CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo Nat.prime_three (by norm_num)
  exact CFSG.RankThree.PartOne.LIT.pRank_le_two_of_det_gl Nat.prime_three hK3 (by simp)
    (StatedSU 3 q K) (fun h hh => CFSG.Open.StatedAPI.det_of_mem_statedSU hh)

theorem card_scalars_statedSU_three_eq_three {K : Type} [Field K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1) :
    Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (2 ^ n) K)) = 3 := by
  rw [CFSG.GH74.GLS.LU.Local.card_scalars_statedSU_three Nat.prime_two hn hK]
  exact Nat.gcd_eq_left h3

theorem pRank_three_le_two_of_cover
    {L S₀ J : Type} [Group L] [Finite L] [Group S₀] [Finite S₀] [Group J]
    (hL : Group.IsPerfect L) (hS₀ : Group.IsPerfect S₀)
    (p₀ : S₀ →* J) (hp₀ : Function.Surjective p₀) (hk₀ : p₀.ker ≤ Subgroup.center S₀)
    (e : L ⧸ Subgroup.center L ≃* J)
    (hZ : Nat.card (Subgroup.center L) = 3) (hk3 : Nat.card p₀.ker = 3)
    {m : ℕ} (hm : Nat.Coprime 3 m) (hM : Nat.card (hopfMultiplier J) = 3 * m)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup S₀) ≤ 2) :
    CFSG.Open.pRank 3 (⊤ : Subgroup L) ≤ 2 := by
  have hq : Function.Surjective (centralQuotientMap e) := centralQuotientMap_surjective e
  have hk : (centralQuotientMap e).ker = Subgroup.center L := centralQuotientMap_ker e
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZp : IsPGroup 3 (Subgroup.center L) := IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
  have hE2 : IsPGroup 3 (centralQuotientMap e).ker := by
    rw [hk]
    exact hZp
  obtain ⟨α, hα, -⟩ := exists_lift_of_coprime_index hS₀ hL p₀ hp₀ hk₀ (centralQuotientMap e) hq hk.le
    Nat.prime_three hE2 m hm (by rw [hM, hk3])
  have hcard : Nat.card S₀ = Nat.card L := by
    rw [card_eq_card_mul_card_ker p₀ hp₀, card_eq_card_mul_card_ker (centralQuotientMap e) hq, hk3,
      hk, hZ]
  obtain ⟨eq⟩ := mulEquiv_of_lift α hα hcard
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eq]
  exact hrank

theorem pRank_three_le_two_of_psl3_cover {L : Type} [Group L] [Finite L] (hL : Group.IsPerfect L)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedSL 3 K))
    (hZ : Nat.card (Subgroup.center L) = 3) (h3 : 3 ∣ Nat.card K - 1)
    {m : ℕ} (hm : Nat.Coprime 3 m)
    (hM : Nat.card (hopfMultiplier (L ⧸ Subgroup.center L)) = 3 * m) :
    CFSG.Open.pRank 3 (⊤ : Subgroup L) ≤ 2 := by
  obtain ⟨p₀, hp₀, hk₀⟩ := CFSG.GH74.GLS.LU.Local.exists_cover_psl_three e
  have hS₀ : Group.IsPerfect SL(3, K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  exact pRank_three_le_two_of_cover hL hS₀ p₀ hp₀ hk₀.le (MulEquiv.refl _) hZ
    (by rw [hk₀]; exact card_center_specialLinear_three h3) hm hM
    pRank_three_le_two_specialLinear_three

theorem pRank_three_le_two_of_psu3_cover {L : Type} [Group L] [Finite L] (hL : Group.IsPerfect L)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedSU 3 (2 ^ n) K))
    (hZ : Nat.card (Subgroup.center L) = 3) (h3 : 3 ∣ 2 ^ n + 1)
    {m : ℕ} (hm : Nat.Coprime 3 m)
    (hM : Nat.card (hopfMultiplier (L ⧸ Subgroup.center L)) = 3 * m) :
    CFSG.Open.pRank 3 (⊤ : Subgroup L) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (k := 2 * n) (by omega) (by rw [hK, ← pow_mul, mul_comm])
  obtain ⟨p₀, hp₀, hk₀⟩ := CFSG.GH74.GLS.LU.Local.exists_cover_psu_three e
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hS₀ : Group.IsPerfect (StatedSU 3 (2 ^ n) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK le_rfl (fun h => by
      simp only [Prod.mk.injEq, true_and] at h
      omega)
  exact pRank_three_le_two_of_cover hL hS₀ p₀ hp₀
    (hk₀.le.trans (CFSG.LieType.Universal.Unitary.statedScalars_subgroupOf_le_center 3 (2 ^ n)))
    (MulEquiv.refl _) hZ
    (by rw [hk₀]; exact card_scalars_statedSU_three_eq_three (by omega) hK h3) hm hM
    pRank_three_le_two_statedSU_three

end CFSG.Quasithin.B69K.OddCovers

end
