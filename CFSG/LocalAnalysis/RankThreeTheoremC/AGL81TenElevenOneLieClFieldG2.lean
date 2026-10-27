module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClField
public import CFSG.RankThree.PartTwo.Sec13.K135GL12Out
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClIndex
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.OutL5Proof

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.LocalAnalysis.RankThreeUC.S15
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
  (autThreePowInner_of_not_three_dvd_outer)

@[expose] def KFactTenElevenOneLieAutFieldG2 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), L.Normal → Open.IsQuasisimple ↥L →
    CFSG.pCore 2 Y = ⊥ → ∀ d : TauCeti.ValidLieTypeIndex, IsRankTwoPlus d.1 →
    (RankTwoList d.1 ∨ RankThreeList d.1) → (∀ q : TauCeti.PrimePower, d.1 ≠ .A 2 q) →
    LieClAut.FieldExponentThree d.1 →
    (∀ q : TauCeti.PrimePower, d.1 = .G2 q → 3 ∣ q.exponent) →
    Nonempty (↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) →
    (∃ u : Y, (∃ k : ℕ, u ^ 3 ^ k = 1) ∧ u ∉ L ⊔ Subgroup.centralizer (L : Set Y)) →
    (∃ T J : Subgroup (↥L ⧸ Subgroup.center ↥L), IsSylowTwoOf T ⊤ ∧
      Subgroup.normalizer (T : Set _) ≤ J ∧ J ≠ Subgroup.normalizer (T : Set _) ∧ J ≠ ⊤) →
    ¬ 3 ∣ Nat.card (Subgroup.centralizer (L : Set Y)) →
    Open.pRank 3 (⊤ : Subgroup Y) = 3 →
    (∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      Open.pRank 3 (Subgroup.centralizer (E : Set Y)) ≤ 2) →
    (∃ N : Subgroup Y, N.Normal ∧ N.index = 3) → False


theorem LieClAut.not_three_dvd_outer_g2 {X : Type} [Group X] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid) (hn : ¬ 3 ∣ q.exponent)
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) : ¬ 3 ∣ Nat.card (Outer X) := by
  have hq : 3 ≤ q.card :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hout := CFSG.RankThree.PartTwo.Sec13.K135GL12.gl12kE_G2_card_outer q hv hq
  rw [← Nat.card_congr (equivalence e).toEquiv] at hout
  intro h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 (h3.trans hout) with h | h
  · omega
  · exact hn h

theorem kFactTenElevenOneLieAutField_of_g2 (hF : KFactTenElevenOneLieAutFieldG2) :
    KFactTenElevenOneLieAutField := by
  intro Y _ _ L hLn hq hO2 d hd hlist hA2 h3 he hu hJ hC3 hrk hE hN
  by_cases hG : ∀ q : TauCeti.PrimePower, d.1 = .G2 q → 3 ∣ q.exponent
  · exact hF Y L hLn hq hO2 d hd hlist hA2 h3 hG he hu hJ hC3 hrk hE hN
  · push Not at hG
    obtain ⟨q, hdq, hn⟩ := hG
    obtain ⟨d, hv⟩ := d
    simp only at hdq
    subst hdq
    haveI := hLn
    obtain ⟨e⟩ := he
    exact LieClAut.false_of_autThreePowInner_of_index hq hC3
      (autThreePowInner_of_not_three_dvd_outer
        (LieClAut.not_three_dvd_outer_g2 q hv hn e)) hN

theorem kFactTenElevenOneLieAutRes_of_fieldG2 (hF : KFactTenElevenOneLieAutFieldG2) :
    KFactTenElevenOneLieAutRes :=
  kFactTenElevenOneLieAutRes_of_field (kFactTenElevenOneLieAutField_of_g2 hF)

end CFSG.LocalAnalysis.RankThreeTheoremC
