module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Competitor

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

section Competitor

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M A H R : Subgroup G}

theorem D2Escape.not_le_of_nclIn_le_R (h : D2Escape p P M A H R) (hglob : AGLGlobal G)
    {H' : Subgroup G} (hJH' : nclIn H R ≤ H') : ¬ H' ≤ M :=
  h.not_le_of_nclIn_le hglob
    ((nclIn_le (h.A_le.trans (le_nclIn h.le_H)) (nclIn_le_self H R)
      (le_normalizer_nclIn H R)).trans hJH')

theorem D2Escape.exists_of_maxTwoLocal_R (h : D2Escape p P M A H R) (hD1p : D1At G p)
    {H' : Subgroup G} (hH' : GLBIsMaxTwoLocal H') (hRH' : R ≤ H') (hH'M : ¬ H' ≤ M) :
    ∃ R' : Subgroup G, D2Escape p P M A H' R' ∧ R ≤ R' := by
  have hprime : p.Prime := h.prime
  have : Fact p.Prime := ⟨hprime⟩
  have hArank : 2 ≤ Open.pRank p A := h.two_le_pRank_A
  have hrank₁ : Open.pRank p (H' ⊓ M) ≤ 2 := by
    by_contra hlt
    exact hH'M (hD1p P M h.maxTwoLocal_M
      ((weakCore_le_fullCore p (P : Subgroup G)).trans h.core_le) H' hH'.1 (by omega))
  obtain ⟨T, hT⟩ := (h.isPGroup.comap_subtype (K := H')).exists_le_sylow
  set R' := (T : Subgroup H').map H'.subtype with hR'
  have hRR' : R ≤ R' := by
    rw [hR', ← Subgroup.map_subgroupOf_eq_of_le hRH']
    exact Subgroup.map_mono hT
  have hAR' : A ≤ R' := h.A_le.trans hRR'
  have hR'p : IsPGroup p R' := T.isPGroup'.map H'.subtype
  have hAM : A ≤ M := h.A_le_M
  have hR'M : R' ≤ M := by
    refine le_of_normalizer_inf_le hR'p fun x hx => ?_
    refine normalizer_le_of_core hprime P h.sylow_le h.core_le inf_le_right
      (hR'p.to_le inf_le_left) ?_ hx.2
    exact hArank.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hprime (le_inf hAR' hAM))
  have hR'H' : R' ≤ H' := Subgroup.map_subtype_le _
  refine ⟨R', ?_, hRR'⟩
  exact {
    prime := hprime
    ne_two := h.ne_two
    sylow_le := h.sylow_le
    core_le := h.core_le
    maxTwoLocal_M := h.maxTwoLocal_M
    maxTwoLocal_H := hH'
    elem := h.elem
    card_A := h.card_A
    core_A := h.core_A
    A_le := hAR'
    le_H := hR'H'
    le_M := hR'M
    isSylow := ⟨T, rfl⟩
    pRank_eq := le_antisymm
      ((CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hprime (le_inf hR'H' hR'M)).trans hrank₁)
      (hArank.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hprime hAR'))
    not_le := hH'M }

theorem D2Escape.eq_of_maxTwoLocal_R (h : D2Escape p P M A H R) (hmax : D2EscapeMax p P M R)
    (hD1p : D1At G p) {H' : Subgroup G} (hH' : GLBIsMaxTwoLocal H') (hRH' : R ≤ H')
    (hH'M : ¬ H' ≤ M) : D2Escape p P M A H' R := by
  obtain ⟨R', h', hRR'⟩ := h.exists_of_maxTwoLocal_R hD1p hH' hRH' hH'M
  have hR'R : R' = R := (Subgroup.eq_of_le_of_card_ge hRR' (hmax A H' R' h')).symm
  exact hR'R ▸ h'

theorem D2Escape.coprime_relIndex_R (h : D2Escape p P M A H R) : p.Coprime (R.relIndex H) := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨T, hT⟩ := h.isSylow
  have hTR : (T : Subgroup H) = R.subgroupOf H := by
    rw [← hT, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  rw [Subgroup.relIndex, ← hTR]
  exact (Nat.Prime.coprime_iff_not_dvd h.prime).mpr T.not_dvd_index

theorem agljCompetitorsOn_d2Escape {J : Subgroup G} (hmax : D2EscapeMax p P M R)
    (hglob : AGLGlobal G) (hD1p : D1At G p) :
    AGLJCompetitorsOn (fun H' => D2Escape p P M A H' R ∧ J ≤ nclIn H' R) R R := by
  rintro H₁ ⟨h₁, hJ₁⟩ H' hH' hJH' hRH'
  have : Fact p.Prime := ⟨h₁.prime⟩
  have hle : nclIn H₁ R ≤ nclIn H' R :=
    nclIn_le_nclIn_of_isSylow h₁.le_H h₁.isPGroup h₁.coprime_relIndex_R hJH'
  have hH'M : ¬ H' ≤ M := h₁.not_le_of_nclIn_le_R hglob hJH'
  exact ⟨⟨h₁.eq_of_maxTwoLocal_R hmax hD1p hH' hRH' hH'M, hJ₁.trans hle⟩, hle⟩

end Competitor

end CFSG.AGLEmbeddingD2
