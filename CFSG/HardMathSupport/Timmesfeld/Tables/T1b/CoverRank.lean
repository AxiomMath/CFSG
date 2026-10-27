module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneSix
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112T1Defs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem one_le_pRank_of_dvd_center {L : Type} [Group L] [Finite L] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card (Subgroup.center L)) :
    1 ≤ CFSG.Open.pRank p (⊤ : Subgroup L) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center L)) p hdvd
  have hzL : orderOf (z : L) = p := by rw [Subgroup.orderOf_coe]; exact hz
  have hzp : (z : L) ^ p = 1 := by rw [← hzL]; exact pow_orderOf_eq_one _
  refine CFSG.SectionRank.le_pRank hp.one_lt (le_top : Subgroup.zpowers (z : L) ≤ ⊤) ?_ ?_
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, i, rfl⟩ := a
      obtain ⟨b, j, rfl⟩ := b
      exact Subtype.ext ((Commute.zpow_zpow_self _ i j).eq)
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzp, one_zpow]
  · rw [pow_one, Nat.card_zpowers, hzL]

theorem pRank_quotient_le_of_le_two {L : Type} [Group L] [Finite L] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hdvd : p ∣ Nat.card (Subgroup.center L))
    (h2 : CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup L) := by
  by_cases h : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L))
  · have := CFSG.Quasithin.H13.L128P.two_le_pRank_of_surjective' hp hp2
      (QuotientGroup.mk' (Subgroup.center L)) (QuotientGroup.mk'_surjective _) h
    omega
  · have := one_le_pRank_of_dvd_center hp hdvd
    omega

@[expose] def LieCoverRankHigh : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → LieCentralQuotient L →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card (Subgroup.center L) →
      3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L)) →
      CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤
        CFSG.Open.pRank p (⊤ : Subgroup L)

theorem lieCoverRank_of_high (h : LieCoverRankHigh) : LieCoverRank := by
  intro L _ _ hq hLC p hp hp2 hdvd
  by_cases h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L))
  · exact h L hq hLC p hp hp2 hdvd h3
  · exact pRank_quotient_le_of_le_two hp hp2 hdvd (by omega)

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
