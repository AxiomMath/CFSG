module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentDefs
public import CFSG.RankThree.PartTwo.KFacts.L34Aut
public import CFSG.Sporadic.Schreier.TitsOuterTwo
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem openPRank_top_le_of_not_dvd {G : Type*} [Group G] [Finite G] {p : ℕ} (m : ℕ)
    (h : ¬ p ^ (m + 1) ∣ Nat.card G) : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ m := by
  apply csSup_le'
  rintro k ⟨E, -, -, hE⟩
  by_contra hk
  exact h ((pow_dvd_pow p (by omega : m + 1 ≤ k)).trans
    (hE ▸ Subgroup.card_subgroup_dvd_card E))

theorem card_mulAut_dvd_outer_mul (L : Type) [Group L] [Finite L] :
    Nat.card (MulAut L) ∣ Nat.card (Outer L) * Nat.card L := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (inner L)]
  exact Nat.mul_dvd_mul_left _ (Subgroup.card_range_dvd _)

theorem pRank_three_mulAut_linThreeFour {K : Type} [Group K] [Finite K] (q : TauCeti.PrimePower)
    (hq2 : q.p = 2) (hqe : q.exponent = 2) (hv : (TauCeti.LieTypeIndex.A 2 q).Valid)
    (e : K ≃* CatGroup ⟨.A 2 q, hv⟩) : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hk : Nat.card (GaloisField q.p q.exponent) = 4 := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', hq2, hqe]
    norm_num
  have e' : K ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
      (GaloisField q.p q.exponent) :=
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 _)
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact (CFSG.RankThree.PartTwo.KFacts.L34.pRank_three_mulAut_of_mulEquiv hk e').le

section Tits


theorem pRank_five_mulAut_tits {K : Type} [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex)
    (hd : d.1 = .tits) (e : K ≃* CatGroup d) :
    CFSG.Open.pRank 5 (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd
  subst hd
  obtain ⟨hT, -, hO, -⟩ := CFSG.Sporadic.Schreier.Tits.CTI_Tits_model_outer_two_part_bound K 2 1
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨e⟩⟩)
  have hdvd : Nat.card (MulAut K) ∣ 2 * 17971200 := by
    have := card_mulAut_dvd_outer_mul K
    rwa [hO, hT] at this
  refine openPRank_top_le_of_not_dvd 2 fun h => ?_
  have := h.trans hdvd
  norm_num at this

theorem offCharAut : OffCharAut := by
  intro K _ _ _ _ d ⟨e⟩ p hp
  rcases hp with ⟨rfl, q, hq2, hqe, hd⟩ | ⟨rfl, hd⟩
  · obtain ⟨d, hv⟩ := d
    change d = .A 2 q at hd
    subst hd
    exact pRank_three_mulAut_linThreeFour q hq2 hqe hv e
  · exact pRank_five_mulAut_tits d hd e

end Tits

end CFSG.AGLEmbedding
