module

public import CFSG.LieType.SeitzGeneration.RegimesOuterNarrow

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

@[expose] def SeitzOuterLowN : Prop :=
  SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ NarrowScope p E

@[expose] def KFactSeitzRankTwoLowN : Prop := SeitzInnerLow ∧ SeitzOuterLowN

theorem SeitzOuterLowN.of_regimes (hC : SeitzOuterLowNarrow)
    (hX : SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ NarrowScope p E ∧
      (¬ IsClassicalIndex d.1 ∨ (p = 3 ∧ IsDFourIndex d.1))) : SeitzOuterLowN :=
  SeitzPlanes.of_cover (fun d p _ _ E hE => by
    by_cases h : IsClassicalIndex d.1 ∧ ¬ (p = 3 ∧ IsDFourIndex d.1)
    · exact Or.inl ⟨hE.1, hE.2, h.1, h.2⟩
    · refine Or.inr ⟨hE.1, hE.2, ?_⟩
      by_cases h1 : IsClassicalIndex d.1
      · exact Or.inr (by by_contra h2; exact h ⟨h1, h2⟩)
      · exact Or.inl h1) hC hX

section Rank

theorem RankLE1.of_pRank {K : Type*} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (h : Open.pRank p (⊤ : Subgroup K) ≤ 1) : RankLE1 p K := by
  intro F hF
  have : Fact p.Prime := ⟨hp⟩
  have hFp : IsPGroup p F := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hF.2 g g.2⟩
  obtain ⟨k, hk⟩ := hFp.exists_card_eq
  have hkle : k ≤ Open.pRank p (⊤ : Subgroup K) := by
    refine le_csSup ⟨Nat.card K, ?_⟩ ⟨F, le_top, hF, hk⟩
    rintro r ⟨B, -, -, hB⟩
    calc r ≤ p ^ r := (Nat.lt_pow_self hp.one_lt).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card K := Subgroup.card_le_card_group B
  rw [hk]
  calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (hkle.trans h)
    _ = p := pow_one p

theorem RankLE2.subgroup {X : Type*} [Group X] {p : ℕ} (h : RankLE2 p X) (T : Subgroup X) :
    RankLE2 p T := by
  intro F hF
  have hF' : IsElemAbelian p (F.map T.subtype) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hF _
  have := h _ hF'
  rwa [Subgroup.card_map_of_injective T.subtype_injective] at this

end Rank

theorem InnerPlane.of_map_congr {K : Type*} [Group K] {d : TauCeti.ValidLieTypeIndex} {p : ℕ}
    (e : K ≃* Cat d) {E : Subgroup (MulAut K)}
    (h : InnerPlane d p (E.map (MulAut.congr e).toMonoidHom)) :
    E ≤ (MulAut.conj : K →* MulAut K).range := by
  have h2 : E.map (MulAut.congr e).toMonoidHom ≤
      (MulAut.conj : K →* MulAut K).range.map (MulAut.congr e).toMonoidHom := by
    rw [map_range_conj_congr e]
    exact h
  exact (Subgroup.map_le_map_iff_of_injective (MulAut.congr e).injective).1 h2

end CFSG.LieType.SeitzGeneration
