module

public import CFSG.LocalAnalysis.RankThreeUC.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem gamma_map_automorphism_le (k p : ℕ) (hp : 1 < p) (R : Subgroup G) (φ : MulAut G) :
    (rankThreeGamma k p R).map φ.toMonoidHom ≤ rankThreeGamma k p (R.map φ.toMonoidHom) := by
  refine map_le_iff_le_comap.mpr ((gamma_le_iff k p R _).mpr fun Q hQR hQ => ?_)
  refine map_le_iff_le_comap.mp ?_
  rw [map_equiv_normalizer_eq]
  exact gamma_normalizer_le k p _ (Q.map φ.toMonoidHom) (map_mono hQR)
    (by rwa [pRank_map_automorphism p hp])

theorem gamma_map_automorphism (k p : ℕ) (hp : 1 < p) (R : Subgroup G) (φ : MulAut G) :
    (rankThreeGamma k p R).map φ.toMonoidHom = rankThreeGamma k p (R.map φ.toMonoidHom) := by
  refine le_antisymm (gamma_map_automorphism_le k p hp R φ) ?_
  refine (map_le_map_iff_of_injective (f := φ.symm.toMonoidHom) φ.symm.injective).mp ?_
  rw [map_automorphism_symm_map]
  have h := gamma_map_automorphism_le k p hp (R.map φ.toMonoidHom) φ.symm
  rwa [map_automorphism_symm_map] at h

structure IsCoreWitness (p : ℕ) (P M : Subgroup G) : Prop where
  maxLocal : rankThreeIsMaxTwoLocal M
  u0 : rankThreeGamma 2 p P ≤ M
  u2 : ∀ H : Subgroup G, IsTwoLocal H → 2 ≤ pRank p (H ⊓ M) → H ≤ M

theorem IsWitness.isCoreWitness {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (hw : IsWitness p P M) : IsCoreWitness p (P : Subgroup G) M :=
  ⟨hw.maxLocal, hw.u0, hw.u2⟩

theorem IsCoreWitness.map {p : ℕ} (hp : 1 < p) {P M : Subgroup G} (hw : IsCoreWitness p P M)
    (φ : MulAut G) : IsCoreWitness p (P.map φ.toMonoidHom) (M.map φ.toMonoidHom) := by
  refine ⟨rankThreeIsMaxTwoLocal_map hw.maxLocal φ, ?_, fun H hH h2 => ?_⟩
  · rw [← gamma_map_automorphism 2 p hp]
    exact map_mono hw.u0
  · have hH' := twoLocal_map_automorphism H hH φ.symm
    have h2' : 2 ≤ pRank p (H.map φ.symm.toMonoidHom ⊓ M) := by
      have hinf : (H ⊓ M.map φ.toMonoidHom).map φ.symm.toMonoidHom =
          H.map φ.symm.toMonoidHom ⊓ M := by
        rw [map_inf_eq _ _ φ.symm.toMonoidHom φ.symm.injective, map_automorphism_symm_map]
      rwa [← hinf, pRank_map_automorphism p hp]
    have hle := map_mono (f := φ.toMonoidHom) (hw.u2 _ hH' h2')
    have hH'' := map_automorphism_symm_map H φ.symm
    rw [MulEquiv.symm_symm] at hH''
    rwa [hH''] at hle

theorem exists_isCoreWitness (hUC : rankThreeUC G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    (Q : Sylow p G) : ∃ M : Subgroup G, IsCoreWitness p (Q : Subgroup G) M := by
  have : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  obtain ⟨P, M, hw⟩ := rankThreeUC_iff.mp hUC p hp
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := G) P Q
  refine ⟨M.map (MulAut.conj g).toMonoidHom, ?_⟩
  have h := hw.isCoreWitness.map (sigmaA_prime p hp).one_lt (MulAut.conj g)
  rwa [← sylow_conjugate_eq_map, hg] at h

theorem IsCoreWitness.normalizer_le (hS : Standing G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {Q : Sylow p G} {M : Subgroup G} (hw : IsCoreWitness p (Q : Subgroup G) M) :
    normalizer ((Q : Subgroup G) : Set G) ≤ M := by
  have h3 : 3 ≤ pRank p (Q : Subgroup G) := selected_sylow_rank_at_least_three hS.rank p hp Q
  exact (gamma_normalizer_le 2 p (Q : Subgroup G) (Q : Subgroup G) le_rfl (by omega)).trans hw.u0

theorem IsCoreWitness.eq_of_le (hS : Standing G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {Q : Sylow p G} {M M' : Subgroup G} (hw : IsCoreWitness p (Q : Subgroup G) M)
    (hM' : rankThreeIsMaxTwoLocal M') (hQM' : (Q : Subgroup G) ≤ M') : M' = M := by
  have h3 : 3 ≤ pRank p (Q : Subgroup G) := selected_sylow_rank_at_least_three hS.rank p hp Q
  have hQM : (Q : Subgroup G) ≤ M := le_normalizer.trans (hw.normalizer_le hS hp)
  have h2 : 2 ≤ pRank p (M' ⊓ M) :=
    (by omega : 2 ≤ 3).trans (h3.trans (pRank_mono p (sigmaA_prime p hp).one_lt (le_inf hQM' hQM)))
  exact (hM'.2 M hw.maxLocal.1 (hw.u2 M' hM'.1 h2)).symm

theorem rankThreeAschCoreLocal_of_rankThreeUC (hUC : rankThreeUC G) :
    rankThreeAschCoreLocal G 2 := by
  refine (aschCoreLocal_iff_one_sylow_per_prime 2).mpr fun p hp => ?_
  obtain ⟨P, M, hw⟩ := rankThreeUC_iff.mp hUC p hp
  exact ⟨P, M, hw.maxLocal.1, (aschCore_le_gamma 2 p (P : Subgroup G)).trans hw.u0⟩

theorem setting_of_rankThreeUC (hS : Standing G) (hUC : rankThreeUC G) : Setting G :=
  ⟨hS.simple, hS.nonab, hS.kProper, hS.charTwo, hS.rank, rankThreeAschCoreLocal_of_rankThreeUC hUC⟩

theorem isCoreWitness_of_isCoreMaxLocal (hS : Standing G) (hUC : rankThreeUC G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M) :
    IsCoreWitness p (P : Subgroup G) M := by
  obtain ⟨M₀, hw⟩ := exists_isCoreWitness hUC hp P
  have h3 : 3 ≤ pRank p (P : Subgroup G) := selected_sylow_rank_at_least_three hS.rank p hp P
  have hPM : (P : Subgroup G) ≤ M :=
    (sylowGroup_le_aschCore 2 p (P : Subgroup G) (by omega) h3).trans hM.2
  rwa [hw.eq_of_le hS hp hM.1 hPM]

theorem fullCoreLocal_of_rankThreeUC (hS : Standing G) (hUC : rankThreeUC G) :
    FullCoreLocal G :=
  fun _ hp _ _ hM => (isCoreWitness_of_isCoreMaxLocal hS hUC hp hM).u0

theorem theoremE_of_rankThreeUC (hS : Standing G) (hUC : rankThreeUC G) : TheoremE G :=
  fun _ hp _ _ hM => (isCoreWitness_of_isCoreMaxLocal hS hUC hp hM).u2

theorem IsWitness.isCoreMaxLocal {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (hw : IsWitness p P M) : IsCoreMaxLocal p P M :=
  ⟨hw.maxLocal, (aschCore_le_gamma 2 p (P : Subgroup G)).trans hw.u0⟩

end CFSG.LocalAnalysis.RankThreeUC
