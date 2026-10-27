module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Escape
public import CFSG.LocalAnalysis.RankThreeTheoremC.StrongEmbeddingCase
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem rankThreeGamma_eq_glbCore (k p : ℕ) (R : Subgroup G) :
    rankThreeGamma k p R = GLBCore p k R :=
  rfl

@[expose] def D2FullCoreAt (G : Type) [Group G] [Finite G] (M : Subgroup G) : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ P : Sylow p G, IsCoreMaxLocal p P M →
    rankThreeGamma 2 p (P : Subgroup G) ≤ M

@[expose] def D2ThreeClauseAt (G : Type) [Group G] [Finite G] (M : Subgroup G) : Prop :=
  3 ∈ rankThreeSigmaA G → ∀ P : Sylow 3 G, IsCoreMaxLocal 3 P M →
    (∀ Q : Subgroup G, Q ≤ (P : Subgroup G) → Q ≠ ⊥ →
        3 ≤ CFSG.Open.pRank 3 (Q ⊔ ((P : Subgroup G) ⊓ Subgroup.centralizer (Q : Set G))) →
        Subgroup.normalizer (Q : Set G) ≤ M) ∧
      (¬ Group.IsSolvable M → rankThreeGamma 1 3 (P : Subgroup G) ≤ M)

theorem d2Escape_exists_of_not_le3 (hS : Setting G) (hD1 : TheoremD1 G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (hPM : rankThreeGamma 2 p (P : Subgroup G) ≤ M) {Q : Subgroup G}
    (hQrank : CFSG.Open.pRank p Q = 2) (hQM : rankThreeGamma 1 p Q ≤ M) {H : Subgroup G}
    (hH : IsTwoLocal H) (hQH : Q ≤ H) (hHM : ¬ H ≤ M) :
    ∃ A H₁ R : Subgroup G, CFSG.AGLEmbeddingD2.D2Escape p P M A H₁ R := by
  have hprime : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hsylow, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hPM' : GLBCore p 2 (P : Subgroup G) ≤ M := hPM
  have hQM' : GLBCore p 1 Q ≤ M := hQM
  have hQle : Q ≤ M := Subgroup.le_normalizer.trans
    ((CFSG.AGLEmbeddingD2.normalizer_le_glbCore p 1 le_rfl (by omega)).trans hQM')
  obtain ⟨A, hAQ, hA, hAcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hprime Q
  rw [hQrank] at hAcard
  have hAM : GLBCore p 1 A ≤ M := (CFSG.AGLEmbeddingD2.glbCore_mono p 1 hAQ).trans hQM'
  have hArank : 2 ≤ CFSG.Open.pRank p A :=
    CFSG.AGLEmbeddingD2.le_pRank_of_isElemAbelian hprime hA hAcard
  obtain ⟨H₁, hHH₁, hH₁⟩ := CFSG.PreuniquenessRankFour.Helpers.exists_maximal_twoLocal hH
  have hH₁M : ¬ H₁ ≤ M := fun hle => hHM (hHH₁.trans hle)
  have hrank₁ : CFSG.Open.pRank p (H₁ ⊓ M) ≤ 2 := by
    by_contra hlt
    exact hH₁M (le_of_three_le_pRank_inf hD1 hp hM hH₁.1 (by omega))
  have hAH₁ : A ≤ H₁ := hAQ.trans (hQH.trans hHH₁)
  have hApGroup : IsPGroup p A := fun x => ⟨1, Subtype.ext (by simpa using hA.2 x x.2)⟩
  obtain ⟨T, hT⟩ := (hApGroup.comap_subtype (K := H₁)).exists_le_sylow
  set R := (T : Subgroup H₁).map H₁.subtype with hR
  have hAR : A ≤ R := by
    rw [hR, ← Subgroup.map_subgroupOf_eq_of_le hAH₁]
    exact Subgroup.map_mono hT
  have hRp : IsPGroup p R := T.isPGroup'.map H₁.subtype
  have hRM : R ≤ M := by
    refine CFSG.AGLEmbeddingD2.le_of_normalizer_inf_le hRp fun x hx => ?_
    refine CFSG.AGLEmbeddingD2.normalizer_le_of_core hprime P hsylow hPM' inf_le_right
      (hRp.to_le inf_le_left) ?_ hx.2
    exact hArank.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hprime
      (le_inf hAR (hAQ.trans hQle)))
  have hRH₁ : R ≤ H₁ := Subgroup.map_subtype_le _
  exact ⟨A, H₁, R, {
    prime := hprime
    ne_two := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp
    sylow_le := hsylow
    core_le := hPM'
    maxTwoLocal_M := hM.1
    maxTwoLocal_H := hH₁
    elem := hA
    card_A := hAcard
    core_A := hAM
    A_le := hAR
    le_H := hRH₁
    le_M := hRM
    isSylow := ⟨T, rfl⟩
    pRank_eq := le_antisymm
      ((CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hprime (le_inf hRH₁ hRM)).trans hrank₁)
      (hArank.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hprime hAR))
    not_le := hH₁M }⟩

@[expose] def D2EscapeCase3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → TheoremD1 G → ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → D2FullCoreAt G M →
    D2ThreeClauseAt G M → ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (A H R : Subgroup G),
      IsCoreMaxLocal p P M → CFSG.AGLEmbeddingD2.D2Escape p P M A H R → False

theorem theoremD2_of_escapeCase3 (hS : Setting G) (hD1 : TheoremD1 G) (hcase : D2EscapeCase3 G) :
    TheoremD2 G := by
  intro M hM ha hb p hp P hMP H R hH hRH hRM hRp hRnc hΓ
  by_contra hHM
  have hprime : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp
  have h2 : 2 ≤ CFSG.Open.pRank p R := two_le_pRank_of_not_isCyclic hprime
    (CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp) hRp hRnc
  by_cases h3 : 3 ≤ CFSG.Open.pRank p R
  · exact hHM (le_of_three_le_pRank_inf hD1 hp hMP hH
      (h3.trans (CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono p hprime.one_lt
        (le_inf hRH hRM))))
  · obtain ⟨A, H₁, R₁, hesc⟩ :=
      d2Escape_exists_of_not_le3 hS hD1 hp hMP (ha p hp P hMP) (by omega) hΓ hH hRH hHM
    exact hcase hS hD1 M hM ha hb p hp P A H₁ R₁ hMP hesc

end CFSG.LocalAnalysis.RankThreeTheoremC
