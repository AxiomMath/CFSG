module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Escape

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem D2Escape.exists_of_not_le (hD1 : D1For G) {p : ℕ} (hp : p ∈ GLBBetaFour G)
    (P : Sylow p G) {M : Subgroup G} (hM : GLBIsMaxTwoLocal M)
    (hPM : GLBCore p 2 (P : Subgroup G) ≤ M) {Q : Subgroup G} (hQrank : pRank p Q = 2)
    (hQM : GLBCore p 1 Q ≤ M) {H : Subgroup G} (hH : IsTwoLocal H) (hQH : Q ≤ H)
    (hHM : ¬ H ≤ M) : ∃ A H₁ R : Subgroup G, D2Escape p P M A H₁ R := by
  have hprime : p.Prime := hp.1
  have : Fact p.Prime := ⟨hprime⟩
  have hPrank : 2 ≤ pRank p (P : Subgroup G) := by
    rw [pRank_sylow_eq_globalRank p hprime P]
    have := betaFour_globalRank hp
    omega
  have hsylow : (P : Subgroup G) ≤ M :=
    Subgroup.le_normalizer.trans ((normalizer_le_glbCore p 2 le_rfl hPrank).trans hPM)
  have hQle : Q ≤ M :=
    Subgroup.le_normalizer.trans ((normalizer_le_glbCore p 1 le_rfl (by omega)).trans hQM)
  obtain ⟨A, hAQ, hA, hAcard⟩ := pRank_attained p hprime Q
  rw [hQrank] at hAcard
  have hAM : GLBCore p 1 A ≤ M := (glbCore_mono p 1 hAQ).trans hQM
  have hArank : 2 ≤ pRank p A := le_pRank_of_isElemAbelian hprime hA hAcard
  obtain ⟨H₁, hHH₁, hH₁⟩ := exists_maximal_twoLocal hH
  have hH₁M : ¬ H₁ ≤ M := fun hle => hHM (hHH₁.trans hle)
  have hrank₁ : pRank p (H₁ ⊓ M) ≤ 2 := by
    by_contra hlt
    exact hH₁M (hD1 p hp P M hM ((weakCore_le_fullCore p (P : Subgroup G)).trans hPM) H₁ hH₁.1
      (by omega))
  have hAH₁ : A ≤ H₁ := hAQ.trans (hQH.trans hHH₁)
  have hApGroup : IsPGroup p A := fun x => ⟨1, Subtype.ext (by simpa using hA.2 x x.2)⟩
  obtain ⟨T, hT⟩ := (hApGroup.comap_subtype (K := H₁)).exists_le_sylow
  set R := (T : Subgroup H₁).map H₁.subtype with hR
  have hAR : A ≤ R := by
    rw [hR, ← Subgroup.map_subgroupOf_eq_of_le hAH₁]
    exact Subgroup.map_mono hT
  have hRp : IsPGroup p R := T.isPGroup'.map H₁.subtype
  have hRM : R ≤ M := by
    refine le_of_normalizer_inf_le hRp fun x hx => ?_
    refine normalizer_le_of_core hprime P hsylow hPM inf_le_right (hRp.to_le inf_le_left)
      ?_ hx.2
    exact hArank.trans (pRank_mono p hprime (le_inf hAR (hAQ.trans hQle)))
  have hRH₁ : R ≤ H₁ := Subgroup.map_subtype_le _
  refine ⟨A, H₁, R, ?_⟩
  exact {
    prime := hprime
    ne_two := hp.2.1
    sylow_le := hsylow
    core_le := hPM
    maxTwoLocal_M := hM
    maxTwoLocal_H := hH₁
    elem := hA
    card_A := hAcard
    core_A := hAM
    A_le := hAR
    le_H := hRH₁
    le_M := hRM
    isSylow := ⟨T, rfl⟩
    pRank_eq := le_antisymm ((pRank_mono p hprime (le_inf hRH₁ hRM)).trans hrank₁)
      (hArank.trans (pRank_mono p hprime hAR))
    not_le := hH₁M }

@[expose] def D2EscapeMax (p : ℕ) (P : Sylow p G) (M R : Subgroup G) : Prop :=
  ∀ A' H' R' : Subgroup G, D2Escape p P M A' H' R' → Nat.card R' ≤ Nat.card R

theorem D2Escape.exists_max {p : ℕ} {P : Sylow p G} {M A H R : Subgroup G}
    (h : D2Escape p P M A H R) :
    ∃ A' H' R' : Subgroup G, D2Escape p P M A' H' R' ∧ D2EscapeMax p P M R' := by
  obtain ⟨⟨A', H', R'⟩, h', hmax⟩ := Set.exists_max_image
    {x : Subgroup G × Subgroup G × Subgroup G | D2Escape p P M x.1 x.2.1 x.2.2}
    (fun x => Nat.card x.2.2) (Set.toFinite _) ⟨⟨A, H, R⟩, h⟩
  exact ⟨A', H', R', h', fun A'' H'' R'' h'' => hmax ⟨A'', H'', R''⟩ h''⟩

@[expose] def D2EscapeCase (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ GLBBetaFour G, ∀ (P : Sylow p G) (M A H R : Subgroup G), D2Escape p P M A H R →
    D2EscapeMax p P M R → False

theorem d2_of_escapeCase (hD1 : D1For G) (hcase : D2EscapeCase G) (p : ℕ)
    (hp : p ∈ GLBBetaFour G) (P : Sylow p G) (M : Subgroup G) (hM : GLBIsMaxTwoLocal M)
    (hPM : GLBCore p 2 (P : Subgroup G) ≤ M) (Q : Subgroup G) (_hQ : IsPGroup p Q)
    (hQrank : pRank p Q = 2) (hQM : GLBCore p 1 Q ≤ M) (H : Subgroup G) (hH : IsTwoLocal H)
    (hQH : Q ≤ H) : H ≤ M := by
  by_contra hHM
  obtain ⟨A, H₁, R, h⟩ :=
    D2Escape.exists_of_not_le hD1 hp P hM hPM hQrank hQM hH hQH hHM
  obtain ⟨A', H', R', h', hmax⟩ := h.exists_max
  exact hcase p hp P M A' H' R' h' hmax

end CFSG.AGLEmbeddingD2
