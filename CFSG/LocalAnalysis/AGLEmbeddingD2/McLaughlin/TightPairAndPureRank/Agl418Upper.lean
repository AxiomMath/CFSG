module

public import CFSG.RankThree.PartOne.Q1327T.Item7L3
public import CFSG.RankThree.PartOne.Q1327T.Item7UBasic
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofL2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CoprimeSylowCyclic
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem pRank_three_psl_two_le_one {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 3 ≤ f) :
    CFSG.pRank 3 (StatedProj (StatedSL 2 K)) ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e := projectiveSpecialLinearGroupEquivStatedProj 2 K
  have : Finite (PSL(2, K)) := inferInstance
  have h7 : 7 ≤ Nat.card K := by
    rw [hK]; exact (Nat.pow_le_pow_right (by norm_num) hf).trans' (by norm_num)
  have h := CFSG.RankThree.PartTwo.Sec4.Res417Three.pRank_le_one_of_isCyclic_sylow
    (X := PSL(2, K)) (p := 3) fun R =>
      CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card K hK h7 3
        (by norm_num) (by rw [hK]; exact Nat.Coprime.pow_right f (by norm_num)) R
  rw [CFSG.RankThree.PartOne.pRank_eq_of_mulEquiv_of_one_lt (by norm_num) e.symm]
  exact h

theorem not_three_dvd_card_scalars {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 0 < n)
    (hK : ¬ 3 ∣ Nat.card K - 1) :
    ¬ 3 ∣ Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := (StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) 3 h3
  have hxS : ((x : StatedSL n K) : GL (Fin n) K) ∈ StatedScalars (Fin n) K := x.2
  obtain ⟨c, hc⟩ := hxS
  have hord : orderOf x = orderOf c := by
    have h1 : orderOf x = orderOf ((x : StatedSL n K) : GL (Fin n) K) := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    rw [h1, ← hc]
    refine orderOf_injective (Matrix.GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K) ?_ c
    intro a b hab
    have h0 := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) hab
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.ext_iff] using h0
  apply hK
  rw [← Nat.card_units, ← hx, hord]
  exact orderOf_dvd_natCard c

theorem orderOf_two_zmod_three : orderOf (2 : ZMod 3) = 2 := by
  have h2 : (2 : ZMod 3) ^ 2 = 1 := by decide
  have h1 : (2 : ZMod 3) ≠ 1 := by decide
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime h2 h1

theorem orderOf_neg_one_zmod_three : orderOf (-1 : ZMod 3) = 2 := by
  have h2 : (-1 : ZMod 3) ^ 2 = 1 := by decide
  have h1 : (-1 : ZMod 3) ≠ 1 := by decide
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime h2 h1

theorem pRank_three_psl_three_le_one {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (h2 : 2 ^ f % 3 = 2) :
    CFSG.pRank 3 (StatedProj (StatedSL 3 K)) ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hm : Nat.card K % 3 = 2 := by rw [hK]; exact h2
  refine CFSG.RankThree.PartOne.Q1327T.pRank_statedProj_statedSL_le_one Nat.prime_three
    (by norm_num) (by omega) (not_three_dvd_card_scalars (by norm_num) (by omega)) ?_
  have hc : ((Nat.card K : ℕ) : ZMod 3) = 2 := by
    rw [← ZMod.natCast_mod, hm]; norm_num
  rw [hc, orderOf_two_zmod_three]

theorem pRank_three_psu_three_le_one {K : Type} [Field K] [Finite K] {e : ℕ}
    (hK : Nat.card K = (2 ^ e) ^ 2) (h1 : 2 ^ e % 3 = 1) :
    CFSG.pRank 3 (StatedProj (StatedSU 3 (2 ^ e) K)) ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.RankThree.PartOne.Q1327T.pRank_statedProj_statedSU_le_one Nat.prime_three
    (by norm_num) (by norm_num) hK (by omega) ?_
  have hc : (((2 ^ e : ℕ)) : ZMod 3) = 1 := by
    rw [← ZMod.natCast_mod, h1]; norm_num
  rw [hc, orderOf_neg_one_zmod_three]

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
