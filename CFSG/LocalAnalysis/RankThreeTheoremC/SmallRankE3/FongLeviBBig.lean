module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviSetting
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SpBlocks
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open TauCeti Subgroup CFSG.Open

theorem le_pRank_three_statedProj_of_card {F : Type} [Field F] [Finite F] {f n : ℕ}
    (hcard : Nat.card F = 2 ^ f) :
    n ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSp n F))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hcard
  refine CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.le_pRank_statedProj_sp
    Nat.prime_three ?_
  rw [hcard, ← pow_mul]
  have h := Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_mul_left 2 f)
  have h22 : (2 : ℕ) ^ 2 - 1 = 3 := by norm_num
  rwa [h22] at h

theorem bBig_false {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ}
    (S : E3Setting K K₀ B z p) {n : ℕ} (hn : 4 ≤ n) {q : PrimePower} (hq2 : q.p = 2)
    (hv : (LieTypeIndex.B n q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.B n q, hv⟩)) : False := by
  obtain ⟨e⟩ := e
  have hK : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B n q, hv⟩) = q.p ^ q.exponent :=
    CFSG.Models.card_fixedField_of (LieTypeIndex.characteristic_B n q)
      (LieTypeIndex.fieldExponent_B n q)
  have hF2 : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B n q, hv⟩) = 2 ^ q.exponent := by
    rw [hK, hq2]
  haveI : Finite ↥(ValidLieTypeIndex.fixedField ⟨.B n q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.B n q, hv⟩
  have h1 := le_pRank_three_statedProj_of_card (n := n) hF2
  have e' := e.trans (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj n q hv
    hq2 (by omega))
  have h3 : CFSG.Open.pRank 3 K ≤ 3 := S.hℓ 3 Nat.prime_three (by norm_num)
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup K,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e'] at h3
  have h4 := le_trans h1 h3
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
