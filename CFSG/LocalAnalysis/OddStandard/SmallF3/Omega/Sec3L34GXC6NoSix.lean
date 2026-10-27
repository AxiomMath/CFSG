module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXC6Def
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.RankThree.PartTwo.Census.OddClassical.LinearTwo

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint
open scoped MatrixGroups

private theorem l34g_charP_three_of_card {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 3 ^ f) : CharP K 3 := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hpc, n, hp, hcard⟩ := FiniteField.card' K
  have hdvd : p ∣ 3 := by
    refine hp.dvd_of_dvd_pow (n := f) ?_
    rw [← hK, Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self p n.ne_zero
  rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd] at hpc
  exact hpc

theorem l34g_c6_of_lieModel_psl2_char3 {Y : Type} [Group Y] {f : ℕ}
    (hY : LieModel Y .PSL 2 3 f) : L34GC6 Y := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hY.statedClassicalModel_of_ne_zero (by norm_num)
  let φ : Y ≃* PSL(2, K) :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  haveI : CharP K 3 := l34g_charP_three_of_card hK
  intro σ _ y u hy hu hyu _ _
  exfalso
  refine CFSG.RankThree.PartTwo.Census.not_commute_PSL_two_char_three (φ u) (φ y) ?_ ?_ ?_
  · rw [MulEquiv.orderOf_eq]
    exact hu
  · rw [MulEquiv.orderOf_eq]
    exact hy
  · rw [← map_mul, ← map_mul, hyu]

end CFSG.OddStandard.SmallF3.Omega
