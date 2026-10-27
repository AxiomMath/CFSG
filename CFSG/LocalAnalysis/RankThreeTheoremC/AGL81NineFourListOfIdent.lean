module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenOtherCfgOf
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallIdent
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Plus

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.NineFour

open CFSG.AGLEmbedding

theorem exists_nineFourIndex_of_isSmallStrongP_of_not {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Group K] (hA : 7 ≤ p → ¬ CFSG.AGLEmbedding.IsAltTwoP p K)
    (hF : p = 5 → ¬ CFSG.AGLEmbedding.IsFi22 K) (h : CFSG.AGLEmbedding.IsSmallStrongP p K) :
    ∃ i : TauCeti.CFSGIndex, IsNineFourIndex p i ∧ Nonempty (K ≃* i.Group) := by
  rcases h with h | h | h | h | h | h
  · obtain ⟨d, ⟨q, hq, hqp, hqe⟩, ⟨e⟩⟩ := h
    exact ⟨.lie d, Or.inl ⟨q, hqp, by omega, hq⟩, ⟨e⟩⟩
  · obtain ⟨d, ⟨q, hqp, -, hq⟩, ⟨e⟩⟩ := h
    exact ⟨.lie d, Or.inr (Or.inl ⟨q, hqp, hq⟩), ⟨e⟩⟩
  · obtain ⟨e⟩ := h
    have h5 : 5 ≤ 2 * p := by have := hp.two_le; omega
    by_cases hp7 : 7 ≤ p
    · exact (hA hp7 ⟨e⟩).elim
    have hp35 : p = 3 ∨ p = 5 := by
      have := hp.two_le
      interval_cases p <;> first | (left; rfl) | (right; rfl) | exact absurd rfl hp2 |
        exact absurd hp (by norm_num)
    refine ⟨.alternating (2 * p) h5, ?_, ⟨e⟩⟩
    rcases hp35 with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  · obtain ⟨hp3, h⟩ := h
    rcases h with ⟨d, ⟨q, hq2, hqe, hq⟩, ⟨e⟩⟩ | e
    · exact ⟨.lie d, Or.inr (Or.inr (Or.inr (Or.inl ⟨hp3, Or.inr ⟨q, hq2, hqe, hq⟩⟩))), ⟨e⟩⟩
    · exact ⟨.sporadic .M11, Or.inl ⟨hp3, rfl⟩, e⟩
  · obtain ⟨hp5, h⟩ := h
    rcases h with ⟨d, hd, ⟨e⟩⟩ | e | e
    · exact ⟨.lie d, Or.inr (Or.inr (Or.inr (Or.inr ⟨hp5, Or.inr hd⟩))), ⟨e⟩⟩
    · exact ⟨.sporadic .McL, Or.inr (Or.inl ⟨hp5, rfl⟩), e⟩
    · exact (hF hp5 e).elim
  · obtain ⟨hp11, e⟩ := h
    exact ⟨.sporadic .J4, Or.inr (Or.inr ⟨hp11, rfl⟩), e⟩

theorem nineFourListGroup_of_identification {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {K : Type}
    [Group K] (hKs : IsSimpleGroup K) (hA : 7 ≤ p → ¬ CFSG.AGLEmbedding.IsAltTwoP p K)
    (hF : p = 5 → ¬ CFSG.AGLEmbedding.IsFi22 K)
    (h : CFSG.AGLEmbedding.IsSmallStrongP p K ∨
      (∃ d : TauCeti.ValidLieTypeIndex,
        ((∃ n : ℕ, 3 ≤ n ∧ CFSG.AGLEmbedding.IsLinTwoIndex p n d) ∨
          (CFSG.AGLEmbedding.IsUnitaryIndex p d ∧ 2 ≤ d.1.fieldExponent) ∨
          CFSG.AGLEmbedding.IsReeGTwoIndex p d) ∧
        Nonempty (K ≃* CFSG.AGLEmbedding.CatGroup d)) ∨
      (p = 5 ∧ CFSG.RankThree.PartOne.Census3.IsoLie K (.suzuki 2))) :
    NineFourListGroup p K := by
  refine ⟨hKs, ?_⟩
  rcases h with hsmall | ⟨d, hd, he⟩ | ⟨hp5', hsz⟩
  · exact exists_nineFourIndex_of_isSmallStrongP_of_not hp (by omega) hA hF hsmall
  · rcases hd with ⟨n, hn, q, hq, hqp, hqe⟩ | ⟨⟨q, hqp, hq⟩, -⟩ | hd
    · exact ⟨.lie d, Or.inl ⟨q, hqp, by omega, hq⟩, he⟩
    · exact ⟨.lie d, Or.inr (Or.inl ⟨q, hqp, hq⟩), he⟩
    · exact ⟨.lie d, Or.inr (Or.inr (Or.inl hd)), he⟩
  · obtain ⟨hv, ⟨e⟩⟩ := hsz
    refine ⟨.lie ⟨.suzuki 2, hv⟩, ?_, ⟨e⟩⟩
    subst p
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩)))

theorem nineFourListGroup_three_of_gls3ConclusionPlus {X : Type} [Group X] [Finite X]
    {K P : Subgroup X} [IsSimpleGroup ↥K]
    (h : CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3ConclusionPlus
      X K P) :
    NineFourListGroup 3 ↥K := by
  obtain ⟨-, -, h3⟩ := h
  rcases h3 with h | h | h | h | h | h | h
  · obtain ⟨q, hq, hI, _⟩ := h
    obtain ⟨hv, ⟨e⟩⟩ := hI
    have h2 : 2 ≤ q.exponent := by
      have h4 : 4 ≤ q.card :=
        ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
          ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).2 rfl
      rw [TauCeti.PrimePower.card_def, hq] at h4
      have hpos := q.exponent_pos
      by_contra hlt
      have h1 : q.exponent = 1 := by omega
      rw [h1] at h4
      norm_num at h4
    exact ⟨inferInstance, .lie ⟨.A 1 q, hv⟩,
      Or.inl ⟨q, hq, h2, rfl⟩, ⟨e⟩⟩
  · obtain ⟨q, hq, hI, _⟩ := h
    obtain ⟨hv, ⟨e⟩⟩ := hI
    exact ⟨inferInstance, .lie ⟨.twistedA 2 q, hv⟩,
      Or.inr (Or.inl ⟨q, hq, rfl⟩), ⟨e⟩⟩
  · obtain ⟨m, hI, _⟩ := h
    obtain ⟨hv, ⟨e⟩⟩ := hI
    exact ⟨inferInstance, .lie ⟨.reeG2 m, hv⟩,
      Or.inr (Or.inr (Or.inl ⟨rfl, m, rfl⟩)), ⟨e⟩⟩
  · let q : TauCeti.PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩
    obtain ⟨hI, _⟩ := h
    obtain ⟨hv, ⟨e⟩⟩ := hI
    have hv' : (TauCeti.LieTypeIndex.A 1 q).Valid := hv
    exact ⟨inferInstance, .lie ⟨.A 1 q, hv'⟩,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨q, rfl, rfl, rfl⟩⟩))), ⟨e⟩⟩
  · obtain ⟨⟨φ, A, hA, hmem⟩, _⟩ := h
    have h6 : 5 ≤ 6 := by norm_num
    exact ⟨inferInstance, .alternating 6 h6, Or.inl ⟨rfl, rfl⟩, ⟨φ⟩⟩
  · let q : TauCeti.PrimePower := ⟨2, 2, Nat.prime_two, by norm_num⟩
    obtain ⟨hI, _⟩ := h
    obtain ⟨hv, ⟨e⟩⟩ := hI
    have hv' : (TauCeti.LieTypeIndex.A 2 q).Valid := hv
    exact ⟨inferInstance, .lie ⟨.A 2 q, hv'⟩,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr ⟨q, rfl, rfl, rfl⟩⟩))), ⟨e⟩⟩
  · obtain ⟨hM, _⟩ := h
    obtain ⟨e⟩ := hM
    exact ⟨inferInstance, .sporadic .M11, Or.inl ⟨rfl, rfl⟩, ⟨e⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.NineFour
