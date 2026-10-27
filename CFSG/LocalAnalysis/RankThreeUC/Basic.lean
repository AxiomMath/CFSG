module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

structure Standing (G : Type) [Group G] [Finite G] : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kProper : IsKProper G
  charTwo : IsCharTwoType G
  rank : evenRank G = 3

structure IsWitness (p : ℕ) (P : Sylow p G) (M : Subgroup G) : Prop where
  maxLocal : rankThreeIsMaxTwoLocal M
  u0 : rankThreeGamma 2 p (P : Subgroup G) ≤ M
  u1 : rankThreeGamma 1 p (P : Subgroup G) ≤ M ∨ rankThreeClauseB M (P : Subgroup G) p ∨
    (p = 3 ∧ rankThreeClauseC M (P : Subgroup G))
  u2 : ∀ H : Subgroup G, IsTwoLocal H → 2 ≤ pRank p (H ⊓ M) → H ≤ M

theorem rankThreeUC_iff : rankThreeUC G ↔
    ∀ p ∈ rankThreeSigmaA G, ∃ (P : Sylow p G) (M : Subgroup G), IsWitness p P M := by
  refine ⟨fun h p hp => ?_, fun h p hp => ?_⟩
  · obtain ⟨P, M, h1, h2, h3, h4⟩ := h p hp
    exact ⟨P, M, h1, h2, h3, h4⟩
  · obtain ⟨P, M, hw⟩ := h p hp
    exact ⟨P, M, hw.maxLocal, hw.u0, hw.u1, hw.u2⟩

omit [Finite G] in
theorem normalizer_eq_of_isMaxTwoLocal {M V : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V) (hMV : M ≤ normalizer (V : Set G)) :
    normalizer (V : Set G) = M :=
  hM.2 _ ⟨V, hV, hV2, rfl⟩ hMV

@[expose] def uniqueSet (M : Subgroup G) : Set (Subgroup G) :=
  {X | X ≤ M ∧ ∀ g : G, X ≤ M.map (MulAut.conj g).toMonoidHom →
    M.map (MulAut.conj g).toMonoidHom = M}

omit [Finite G] in
theorem normalizer_le_of_mem_uniqueSet {M X : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    (hX : X ∈ uniqueSet M) : normalizer (X : Set G) ≤ M := by
  intro g hg
  have hconj : X.map (MulAut.conj g).toMonoidHom = X := mem_normalizer_iff_map_conj_eq.mp hg
  have hXg : X ≤ M.map (MulAut.conj g).toMonoidHom := hconj ▸ map_mono hX.1
  rw [← maxTwoLocal_self_normalizing M hM]
  exact mem_normalizer_iff_map_conj_eq.mpr (hX.2 g hXg)

omit [Finite G] in
theorem mem_uniqueSet_of_forall {M X : Subgroup G} (hM : rankThreeIsMaxTwoLocal M) (hXM : X ≤ M)
    (h : ∀ H : Subgroup G, rankThreeIsMaxTwoLocal H → X ≤ H → H = M) : X ∈ uniqueSet M :=
  ⟨hXM, fun _ hXg => h _ (rankThreeIsMaxTwoLocal_map hM _) hXg⟩

omit [Finite G] in
theorem mem_uniqueSet_of_le {M X Y : Subgroup G} (hX : X ∈ uniqueSet M) (hXY : X ≤ Y)
    (hYM : Y ≤ M) : Y ∈ uniqueSet M :=
  ⟨hYM, fun g hYg => hX.2 g (hXY.trans hYg)⟩

namespace IsWitness

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem normalizer_sylow_le (hS : Standing G) (hp : p ∈ rankThreeSigmaA G)
    (hw : IsWitness p P M) : normalizer ((P : Subgroup G) : Set G) ≤ M := by
  have h3 : 3 ≤ pRank p (P : Subgroup G) := selected_sylow_rank_at_least_three hS.rank p hp P
  exact (gamma_normalizer_le 2 p (P : Subgroup G) (P : Subgroup G) le_rfl (by omega)).trans hw.u0

theorem sylow_le (hS : Standing G) (hp : p ∈ rankThreeSigmaA G) (hw : IsWitness p P M) :
    (P : Subgroup G) ≤ M :=
  le_normalizer.trans (hw.normalizer_sylow_le hS hp)

theorem pRank_eq_three (hS : Standing G) (hp : p ∈ rankThreeSigmaA G) (hw : IsWitness p P M) :
    pRank p (P : Subgroup G) = 3 ∧ pRank p M = 3 := by
  have hprime := sigmaA_prime p hp
  have h3 := selected_sylow_rank_at_least_three hS.rank p hp P
  have hPM := pRank_mono p hprime.one_lt (hw.sylow_le hS hp)
  have hM := local_pRank_le_evenRank p hprime (sigmaA_odd p hp) M hw.maxLocal.1
  rw [hS.rank] at hM
  omega

theorem le_of_le_of_two_le_pRank (hp : p ∈ rankThreeSigmaA G) (hw : IsWitness p P M)
    {R H : Subgroup G} (hRM : R ≤ M) (hR : 2 ≤ pRank p R) (hH : IsTwoLocal H) (hRH : R ≤ H) :
    H ≤ M :=
  hw.u2 H hH (hR.trans (pRank_mono p (sigmaA_prime p hp).one_lt (le_inf hRH hRM)))

theorem eq_of_le_of_two_le_pRank (hp : p ∈ rankThreeSigmaA G) (hw : IsWitness p P M)
    {R H : Subgroup G} (hRM : R ≤ M) (hR : 2 ≤ pRank p R) (hH : rankThreeIsMaxTwoLocal H)
    (hRH : R ≤ H) : H = M :=
  (hH.2 M hw.maxLocal.1 (hw.le_of_le_of_two_le_pRank hp hRM hR hH.1 hRH)).symm

theorem mem_uniqueSet (hp : p ∈ rankThreeSigmaA G) (hw : IsWitness p P M) {R : Subgroup G}
    (hRM : R ≤ M) (hR : 2 ≤ pRank p R) : R ∈ uniqueSet M :=
  mem_uniqueSet_of_forall hw.maxLocal hRM fun _ hH hRH =>
    hw.eq_of_le_of_two_le_pRank hp hRM hR hH hRH

theorem normalizer_le (hp : p ∈ rankThreeSigmaA G) (hw : IsWitness p P M) {R : Subgroup G}
    (hRM : R ≤ M) (hR : 2 ≤ pRank p R) : normalizer (R : Set G) ≤ M :=
  normalizer_le_of_mem_uniqueSet hw.maxLocal (hw.mem_uniqueSet hp hRM hR)

end IsWitness

end CFSG.LocalAnalysis.RankThreeUC
