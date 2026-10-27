module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallIdent
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.AGLEmbedding

open CFSG.LocalAnalysis.RankThreeTheoremC (IsRankTwoSEGroup)
open CFSG.LocalAnalysis.ComponentInitial
  (unique_field_nine_projective_linear_alternating_six_isomorphism)
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem openPRank_le_one_of_isCyclic {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (T : Subgroup K) [IsCyclic T] : CFSG.Open.pRank p T ≤ 1 := by
  unfold CFSG.Open.pRank
  apply csSup_le'
  rintro k ⟨E, hET, hE, hcard⟩
  have hexp : Monoid.exponent (E.subgroupOf T) ∣ p := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    apply Subtype.ext
    apply Subtype.ext
    have hx : ((x : T) : K) ∈ E := x.2
    simpa using hE.2 _ hx
  rw [IsCyclic.exponent_eq_card] at hexp
  have hc : Nat.card (E.subgroupOf T) = p ^ k := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hET).toEquiv, hcard]
  rw [hc] at hexp
  have h1 : p ^ k ∣ p ^ 1 := by simpa using hexp
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h1

theorem nonempty_mulEquiv_psl2GF_nine_of_alt {K : Type} [Group K]
    (e : K ≃* alternatingGroup (Fin (2 * 3))) : Nonempty (K ≃* PSL2GF 3 2) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 2) = 9 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 3 2 (by norm_num)]
    norm_num
  obtain ⟨f⟩ := unique_field_nine_projective_linear_alternating_six_isomorphism (GaloisField 3 2)
    hcard
  exact ⟨e.trans f.symm⟩

theorem isRankTwoSEGroup_of_isSmallStrongP {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type}
    [Group K] (h : IsSmallStrongP p K) : IsRankTwoSEGroup p K := by
  have : Fact p.Prime := ⟨hp⟩
  rcases h with h | h | h | ⟨h3, h⟩ | ⟨h5, h⟩ | ⟨h11, h⟩
  · obtain ⟨d, hd, ⟨e⟩⟩ := h
    obtain ⟨f⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
    exact Or.inl ⟨⟨hp⟩, ⟨e.trans f⟩⟩
  · obtain ⟨⟨d, hv⟩, ⟨q, hqp, hq1, hd⟩, ⟨e⟩⟩ := h
    change d = .twistedA 2 q at hd
    subst hd
    exact Or.inr (Or.inl ⟨q, hqp, hq1, hv, ⟨e⟩⟩)
  · obtain ⟨e⟩ := h
    by_cases h3 : p = 3
    · subst h3
      obtain ⟨f⟩ := nonempty_mulEquiv_psl2GF_nine_of_alt e
      exact Or.inl ⟨⟨hp⟩, ⟨f⟩⟩
    · have h5 : 5 ≤ p := by
        by_contra hlt
        have h234 : p = 2 ∨ p = 3 ∨ p = 4 := by have := hp.two_le; omega
        rcases h234 with rfl | rfl | rfl
        · exact hp2 rfl
        · exact h3 rfl
        · exact absurd hp (by norm_num)
      exact Or.inr (Or.inr (Or.inl ⟨h5, ⟨e⟩⟩))
  · rcases h with ⟨⟨d, hv⟩, ⟨q, hq2, hqe, hd⟩, ⟨e⟩⟩ | h
    · change d = .A 2 q at hd
      subst hd
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, Or.inl ⟨q, hq2, hqe, hv, ⟨e⟩⟩⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, Or.inr h⟩)))
  · rcases h with ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ | h | h
    · change d = .tits at hd
      subst hd
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h5, Or.inl ⟨hv, ⟨e⟩⟩⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h5, Or.inr (Or.inl h)⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h5, Or.inr (Or.inr h)⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h11, h⟩))))

end CFSG.AGLEmbedding
