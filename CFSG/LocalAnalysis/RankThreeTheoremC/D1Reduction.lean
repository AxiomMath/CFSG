module

public import CFSG.LocalAnalysis.AGLEmbedding.Extremal
public import CFSG.LocalAnalysis.RankThreeTheoremC.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def D1MaxCase3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G),
    IsCoreMaxLocal p P M → ∀ H : Subgroup G, rankThreeIsMaxTwoLocal H → ∀ R : Sylow p H,
      (R : Subgroup H).map H.subtype ≤ P → 3 ≤ pRank p ((R : Subgroup H).map H.subtype) → H ≤ M

@[expose] def D1ExtremalCase3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G),
    IsCoreMaxLocal p P M → ∀ H R : Subgroup G, CFSG.AGLEmbedding.D1Extremal p P M H R → False

theorem d1Escape_of_maxCase3 {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G}
    {M : Subgroup G} (hM : IsCoreMaxLocal p P M) {H : Subgroup G}
    (hH : rankThreeIsMaxTwoLocal H) (T : Sylow p H)
    (hTP : (T : Subgroup H).map H.subtype ≤ P)
    (hTrank : 3 ≤ pRank p ((T : Subgroup H).map H.subtype)) (hnot : ¬ H ≤ M) :
    CFSG.AGLEmbedding.D1Escape p P M H ((T : Subgroup H).map H.subtype) where
  prime := sigmaA_prime p hp
  ne_two := sigmaA_odd p hp
  sylow_le := by
    have hprime := sigmaA_prime p hp
    have hPrank : 3 ≤ pRank p (P : Subgroup G) := by
      rw [pRank_sylow_eq_globalRank p hprime P]
      exact hTrank.trans (pRank_mono p hprime le_top)
    exact (subgroup_le_weakCore_of_rank p hprime _ hPrank).trans hM.2
  weakCore_le := hM.2
  maxTwoLocal_M := hM.1
  maxTwoLocal_H := hH
  le_H := Subgroup.map_subtype_le _
  le_P := hTP
  isSylow := ⟨T, rfl⟩
  three_le_pRank := hTrank
  not_le := hnot

theorem theoremD1_of_maxCase3 (hS : Setting G) (h : D1MaxCase3 G) : TheoremD1 G := by
  intro p hp P M hMloc hcore hmax H hH hHM
  exact CFSG.AGLEmbedding.le_of_maxSylowCase (sigmaA_prime p hp) P hcore
    (h hS p hp P M ⟨⟨hMloc, fun K hK hMK => hmax K hK (hcore.trans hMK) hMK⟩, hcore⟩) hH hHM

theorem d1MaxCase3_of_extremalCase3 (h : D1ExtremalCase3 G) : D1MaxCase3 G := by
  intro hS p hp P M hM H hH R hRP hRrank
  by_contra hnot
  obtain ⟨K, R', hext⟩ := (d1Escape_of_maxCase3 hp hM hH R hRP hRrank hnot).exists_extremal
  exact h hS p hp P M hM K R' hext

theorem theoremD1_of_extremalCase3 (hS : Setting G) (h : D1ExtremalCase3 G) : TheoremD1 G :=
  theoremD1_of_maxCase3 hS (d1MaxCase3_of_extremalCase3 h)

theorem d1ExtremalCase3_of_theoremD1 (hD1 : TheoremD1 G) : D1ExtremalCase3 G := by
  intro _ p hp P M hM H R hext
  exact hext.not_le (le_of_three_le_pRank_inf hD1 hp hM hext.maxTwoLocal_H.1
    hext.three_le_pRank_inf)

end CFSG.LocalAnalysis.RankThreeTheoremC
