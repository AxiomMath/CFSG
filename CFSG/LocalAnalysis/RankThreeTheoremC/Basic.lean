module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoreConjugacy

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

structure Setting (G : Type) [Group G] [Finite G] : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kProper : IsKProper G
  charTwo : IsCharTwoType G
  rank : evenRank G = 3
  pre : rankThreeAschCoreLocal G 2

@[expose] def IsCoreMaxLocal (p : ℕ) (P : Sylow p G) (M : Subgroup G) : Prop :=
  rankThreeIsMaxTwoLocal M ∧ rankThreeAschCore 2 p (P : Subgroup G) ≤ M

@[expose] def TheoremD1 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G), IsTwoLocal M →
    rankThreeAschCore 2 p (P : Subgroup G) ≤ M →
    (∀ K : Subgroup G, IsTwoLocal K → rankThreeAschCore 2 p (P : Subgroup G) ≤ K → M ≤ K →
      K = M) →
    ∀ H : Subgroup G, IsTwoLocal H → 3 ≤ pRank p (H ⊓ M) → H ≤ M

@[expose] def FullCoreLocal (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G), IsCoreMaxLocal p P M →
    rankThreeGamma 2 p (P : Subgroup G) ≤ M

@[expose] def AlmostStrongEmbedding (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G), IsCoreMaxLocal p P M →
    rankThreeGamma 1 p (P : Subgroup G) ≤ M ∨ rankThreeClauseB M (P : Subgroup G) p ∨
      (p = 3 ∧ rankThreeClauseC M (P : Subgroup G))

@[expose] def TheoremE (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G), IsCoreMaxLocal p P M →
    ∀ H : Subgroup G, IsTwoLocal H → 2 ≤ pRank p (H ⊓ M) → H ≤ M

omit [Finite G] in
theorem rankThreeIsMaxTwoLocal_map {M : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    (φ : MulAut G) : rankThreeIsMaxTwoLocal (M.map φ.toMonoidHom) := by
  refine ⟨twoLocal_map_automorphism M hM.1 φ, fun H hH hMH => ?_⟩
  have hH' := twoLocal_map_automorphism H hH φ.symm
  have hMH' := Subgroup.map_mono (f := φ.symm.toMonoidHom) hMH
  rw [map_automorphism_symm_map] at hMH'
  have heq := hM.2 _ hH' hMH'
  rw [← heq]
  have := map_automorphism_symm_map H φ.symm
  rw [MulEquiv.symm_symm] at this
  exact this.symm

theorem exists_isCoreMaxLocal (hS : Setting G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    (P : Sylow p G) :
    ∃ M : Subgroup G, IsCoreMaxLocal p P M ∧ (P : Subgroup G) ≤ M ∧
      Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M ∧
      pRank p (P : Subgroup G) = 3 ∧ pRank p M = 3 := by
  obtain ⟨M, hmax, hcore, hnorm, hPM, hP3, hM3⟩ :=
    selected_coreLocal_all_sylows_have_maximal_overgroup hS.rank hS.pre p hp P
  exact ⟨M, ⟨hmax, hcore⟩, hPM, hnorm, hP3, hM3⟩

theorem sylow_le_of_isCoreMaxLocal (hS : Setting G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M) :
    (P : Subgroup G) ≤ M ∧ pRank p (P : Subgroup G) = 3 := by
  have hrank := selected_sylow_rank_at_least_three hS.rank p hp P
  have hPM := (sylowGroup_le_aschCore 2 p (P : Subgroup G) (by omega) hrank).trans hM.2
  have hupper := (pRank_mono p (sigmaA_prime p hp).one_lt hPM).trans
    (local_pRank_le_evenRank p (sigmaA_prime p hp) (sigmaA_odd p hp) M hM.1.1)
  exact ⟨hPM, by rw [hS.rank] at hupper; omega⟩

theorem le_of_three_le_pRank_inf (hD1 : TheoremD1 G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M) {H : Subgroup G}
    (hH : IsTwoLocal H) (hrank : 3 ≤ pRank p (H ⊓ M)) : H ≤ M :=
  hD1 p hp P M hM.1.1 hM.2 (fun K hK _ hMK => hM.1.2 K hK hMK) H hH hrank

theorem eq_of_isMaxTwoLocal_of_three_le_pRank (hD1 : TheoremD1 G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {R H : Subgroup G} (hRM : R ≤ M) (hR : 3 ≤ pRank p R) (hH : rankThreeIsMaxTwoLocal H)
    (hRH : R ≤ H) : H = M := by
  have hHM : H ≤ M := le_of_three_le_pRank_inf hD1 hp hM hH.1
    (hR.trans (pRank_mono p (sigmaA_prime p hp).one_lt (le_inf hRH hRM)))
  exact (hH.2 M hM.1.1 hHM).symm

theorem normalizer_le_of_three_le_pRank (hD1 : TheoremD1 G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {R : Subgroup G} (hRM : R ≤ M) (hR : 3 ≤ pRank p R) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  intro g hg
  have hconj : R.map (MulAut.conj g).toMonoidHom = R :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hRg : R ≤ M.map (MulAut.conj g).toMonoidHom := hconj ▸ Subgroup.map_mono hRM
  have hle : M.map (MulAut.conj g).toMonoidHom ≤ M :=
    le_of_three_le_pRank_inf hD1 hp hM (twoLocal_map_automorphism M hM.1.1 _)
      (hR.trans (pRank_mono p (sigmaA_prime p hp).one_lt (le_inf hRg hRM)))
  have heq : M.map (MulAut.conj g).toMonoidHom = M :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  rw [← maxTwoLocal_self_normalizing M hM.1]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

theorem rankThreeUC_of_parts (hS : Setting G) (hU0 : FullCoreLocal G)
    (hU1 : AlmostStrongEmbedding G) (hU2 : TheoremE G) : rankThreeUC G := by
  intro p hp
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  obtain ⟨M, hM, -⟩ := exists_isCoreMaxLocal hS hp P
  exact ⟨P, M, hM.1, hU0 p hp P M hM, hU1 p hp P M hM, hU2 p hp P M hM⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
