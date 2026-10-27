module

public import CFSG.LieType.SeitzGeneration.RegimesExc

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

@[expose] def RankLE1 (p : ℕ) (K : Type*) [Group K] : Prop :=
  ∀ F : Subgroup K, IsElemAbelian p F → Nat.card F ≤ p

theorem RankLE1.rankLE2 {K : Type*} [Group K] {p : ℕ} (h : RankLE1 p K) : RankLE2 p K :=
  fun F hF => (h F hF).trans (Nat.le_self_pow two_ne_zero p)

theorem RankLE1.of_mulEquiv {K L : Type*} [Group K] [Group L] (e : K ≃* L) {p : ℕ}
    (h : RankLE1 p K) : RankLE1 p L := by
  intro F hF
  have hF' : IsElemAbelian p (F.map e.symm.toMonoidHom) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hF _
  have := h _ hF'
  rwa [Subgroup.card_map_of_injective e.symm.injective] at this

@[expose] def PlaneRank2 {K : Type*} [Group K] (p : ℕ) (E : Subgroup (MulAut K)) : Prop :=
  RankLE2 p ↥((MulAut.conj : K →* MulAut K).range ⊔ E)

@[expose] def NarrowScope {K : Type*} [Group K] (p : ℕ) (E : Subgroup (MulAut K)) : Prop :=
  RankLE2 p K ∧ (RankLE1 p K ∨ PlaneRank2 p E)

theorem map_range_conj_congr {K L : Type*} [Group K] [Group L] (e : K ≃* L) :
    (MulAut.conj : K →* MulAut K).range.map (MulAut.congr e).toMonoidHom =
      (MulAut.conj : L →* MulAut L).range := by
  ext x
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨e g, (mulAut_congr_conj e g).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨MulAut.conj (e.symm g), ⟨e.symm g, rfl⟩, by simpa using mulAut_congr_conj e (e.symm g)⟩

theorem PlaneRank2.map_congr {K L : Type*} [Group K] [Group L] (e : K ≃* L) {p : ℕ}
    {E : Subgroup (MulAut K)} (h : PlaneRank2 p E) :
    PlaneRank2 p (E.map (MulAut.congr e).toMonoidHom) := by
  unfold PlaneRank2 at h ⊢
  rw [← map_range_conj_congr e, ← Subgroup.map_sup]
  exact RankLE2.of_mulEquiv
    (Subgroup.equivMapOfInjective _ (MulAut.congr e).toMonoidHom (MulAut.congr e).injective) h

theorem NarrowScope.map_congr {K L : Type*} [Group K] [Group L] (e : K ≃* L) {p : ℕ}
    {E : Subgroup (MulAut K)} (h : NarrowScope p E) :
    NarrowScope p (E.map (MulAut.congr e).toMonoidHom) :=
  ⟨RankLE2.of_mulEquiv e h.1, h.2.imp (RankLE1.of_mulEquiv e) (PlaneRank2.map_congr e)⟩

@[expose] def SeitzOuterLowNarrow : Prop :=
  SeitzPlanes fun d p E =>
    ¬ InnerPlane d p E ∧ NarrowScope p E ∧ IsClassicalIndex d.1 ∧ ¬ (p = 3 ∧ IsDFourIndex d.1)

theorem SeitzOuterLowClassical.narrow (h : SeitzOuterLowClassical) : SeitzOuterLowNarrow :=
  SeitzPlanes.mono (fun _ _ _ hE => ⟨hE.1, hE.2.1.1, hE.2.2⟩) h

end CFSG.LieType.SeitzGeneration
