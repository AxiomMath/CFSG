module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48NCentStep
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallCentralizer
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48NDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1Sp48NInvolves {G : Type} [Group G] [Finite G] (H : Subgroup G) (d : G) : Prop :=
  ∃ (W : Subgroup G) (L : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (φ : W →* L),
    W ≤ Subgroup.centralizer ({d} : Set G) ∧ Function.Surjective φ ∧ IsSimpleGroup L ∧
    ⁅L, L⁆ = L ∧ IsCaseTwoGroup 3 L ∧ ∃ x ∈ L, x ≠ 1 ∧ x ^ 3 = 1

structure D1Sp48NCentData {G : Type} [Group G] [Finite G] (M H R : Subgroup G) (z₁ z₂ σ : G) :
    Prop where
  z₁_mem : z₁ ∈ centerOf R
  z₂_mem : z₂ ∈ centerOf R
  order₁ : orderOf z₁ = 3
  order₂ : orderOf z₂ = 3
  inf_eq_bot : Subgroup.zpowers z₁ ⊓ Subgroup.zpowers z₂ = ⊥
  σ_mem : σ ∈ H ⊓ M
  σ_norm : σ ∈ Subgroup.normalizer (R : Set G)
  σ₁ : σ * z₁ * σ⁻¹ ∈ Subgroup.zpowers z₂
  σ₂ : σ * z₂ * σ⁻¹ ∈ Subgroup.zpowers z₁
  outside : ∀ d ∈ centerOf R, d ∉ Subgroup.zpowers z₁ → d ∉ Subgroup.zpowers z₂ →
    ¬ Subgroup.centralizer ({d} : Set G) ⊓ H ≤ M
  involve : ∀ d ∈ centerOf R, d ∉ Subgroup.zpowers z₁ → d ∉ Subgroup.zpowers z₂ →
    D1Sp48NInvolves H d
  pRank_le : Open.pRank 3 R ≤ 3

@[expose] def D1Sp48NCMSide : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R X U A V : Subgroup G}
    {z₁ z₂ σ : G}, D1Local 3 P M → D1Extremal 3 P M H R → D1Sp48NData P M H R X U A V →
    D1Sp48NCentData M H R z₁ z₂ σ → CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥ → False

@[expose] def D1Sp48NCentResidue : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R X U A V : Subgroup G} {d : G},
    D1Local 3 P M → D1Extremal 3 P M H R → D1Sp48NData P M H R X U A V →
    CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥ → d ∈ centerOf R → d ≠ 1 →
    ¬ Subgroup.centralizer ({d} : Set G) ⊓ H ≤ M →
    (∃ Y : Subgroup G, IsPGroup 3 Y ∧ R < Y ∧ Y ≤ M ⊓ Subgroup.centralizer ({d} : Set G)) →
    D1Sp48NInvolves H d →
    pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) = ⊥ → False

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}

theorem D1Sp48NCentData.exists_outside {z₁ z₂ σ : G} (hloc : D1Local 3 P M)
    (hext : D1Extremal 3 P M H R) (hc : D1Sp48NCentData M H R z₁ z₂ σ) :
    ∃ d ∈ centerOf R, d ≠ 1 ∧ ¬ Subgroup.centralizer ({d} : Set G) ⊓ H ≤ M ∧
      D1Sp48NInvolves H d ∧
      ∃ Y : Subgroup G, IsPGroup 3 Y ∧ R < Y ∧ Y ≤ M ⊓ Subgroup.centralizer ({d} : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRP : R ≠ (P : Subgroup G) := by
    intro h
    have h4 := betaFour_all_sylows_rank_ge_four hloc.beta P
    rw [← h] at h4
    have := hc.pRank_le
    omega
  set Q : Subgroup G := (P : Subgroup G) ⊓ Subgroup.normalizer (R : Set G) with hQ
  have hQp : IsPGroup 3 Q := P.isPGroup'.to_le inf_le_left
  have hRQ : R < Q := by
    refine lt_of_le_of_ne (le_inf hext.le_P Subgroup.le_normalizer) fun heq => hRP ?_
    exact (eq_of_isPGroup_of_le_of_normalizer P.isPGroup' hext.le_P
      fun g hg hgN => heq ▸ ⟨hg, hgN⟩).symm
  obtain ⟨d, hd, hd1, hd2, Y, hY, hRY, hYN, hYC⟩ := Sp48NCent.exists_outside_le_centralizer hQp hRQ
    inf_le_right hc.z₁_mem hc.z₂_mem hc.order₁ hc.order₂ hc.inf_eq_bot hc.σ_norm hc.σ₁ hc.σ₂
  refine ⟨d, hd, fun h => hd1 (h ▸ Subgroup.one_mem _), hc.outside d hd hd1 hd2,
    hc.involve d hd hd1 hd2, Y, hY, hRY, le_inf (hYN.trans hext.normalizer_le) hYC⟩

theorem D1Extremal.centralizer_le_of_twoCore_ne_bot (hext : D1Extremal 3 P M H R) {d : G}
    {Y : Subgroup G} (hY : IsPGroup 3 Y) (hRY : R < Y)
    (hYC : Y ≤ M ⊓ Subgroup.centralizer ({d} : Set G))
    (hO : pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) ≠ ⊥) :
    Subgroup.centralizer ({d} : Set G) ≤ M := by
  set C := Subgroup.centralizer ({d} : Set G)
  have hCN : C ≤ Subgroup.normalizer (pCoreOf 2 C : Set G) := localGroup_le_normalizer_pCoreOf 2 C
  have h2 : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 C : Set G)) :=
    ⟨pCoreOf 2 C, hO, PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 C, rfl⟩
  have hrank : 3 ≤ Open.pRank 3 Y := hext.three_le_pRank.trans (pRank_mono 3 hext.prime hRY.le)
  exact hCN.trans (hext.le_of_card_lt (hYC.trans inf_le_left) hY hrank
    (Subgroup.card_lt_of_lt hRY) h2 ((hYC.trans inf_le_right).trans hCN))

theorem d1Sp48NCMSide_of (hres : D1Sp48NCentResidue) : D1Sp48NCMSide := by
  intro G _ _ P M H R X U A V z₁ z₂ σ hloc hext hd hc hO3
  obtain ⟨d, hdZ, hd1, hdout, hinv, Y, hY, hRY, hYC⟩ := hc.exists_outside hloc hext
  by_cases hO : pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) = ⊥
  · exact hres hloc hext hd hO3 hdZ hd1 hdout ⟨Y, hY, hRY, hYC⟩ hinv hO
  · exact hdout (inf_le_left.trans (hext.centralizer_le_of_twoCore_ne_bot hY hRY hYC hO))

end CFSG.AGLEmbedding
