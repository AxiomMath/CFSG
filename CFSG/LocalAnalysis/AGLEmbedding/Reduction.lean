module

public import CFSG.LocalAnalysis.AGLEmbedding.Statements
public import CFSG.LocalAnalysis.PreuniquenessRankFour.SamePrimeAction
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoreConjugacy

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

variable {G : Type*} [Group G]

theorem glbIsMaxTwoLocal_map_mulAut {H : Subgroup G} (hH : GLBIsMaxTwoLocal H)
    (σ : MulAut G) : GLBIsMaxTwoLocal (H.map σ.toMonoidHom) := by
  refine ⟨CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_map_automorphism H hH.1 σ, ?_⟩
  intro K hK hHK
  have hback : H ≤ K.map σ.symm.toMonoidHom := by
    have hmap := Subgroup.map_mono (f := σ.symm.toMonoidHom) hHK
    rwa [CFSG.RankThreeCoreUniqueness.Helpers.map_automorphism_symm_map] at hmap
  have heq := hH.2 _
    (CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_map_automorphism K hK σ.symm) hback
  have hK : (K.map σ.symm.toMonoidHom).map σ.toMonoidHom = K := by
    simpa only [MulEquiv.symm_symm] using
      CFSG.RankThreeCoreUniqueness.Helpers.map_automorphism_symm_map K σ.symm
  rw [← hK, heq]

theorem le_of_map_conj_le {K M : Subgroup G} {m : G} (hm : m ∈ M)
    (hle : K.map (MulAut.conj m).toMonoidHom ≤ M) : K ≤ M := by
  intro x hx
  have hmx : m * x * m⁻¹ ∈ M := hle (Subgroup.mem_map_of_mem _ hx)
  simpa [mul_assoc] using M.mul_mem (M.mul_mem (M.inv_mem hm) hmx) hm

variable [Finite G]

noncomputable def sylowMapMulAut {p : ℕ} [Fact p.Prime] {H : Subgroup G} (R : Sylow p H)
    (σ : MulAut G) : Sylow p (H.map σ.toMonoidHom) :=
  R.mapSurjective (σ.toMonoidHom.subgroupMap_surjective H)

theorem map_subtype_sylowMapMulAut {p : ℕ} [Fact p.Prime] {H : Subgroup G} (R : Sylow p H)
    (σ : MulAut G) :
    ((sylowMapMulAut R σ : Sylow p (H.map σ.toMonoidHom)) :
        Subgroup (H.map σ.toMonoidHom)).map (H.map σ.toMonoidHom).subtype =
      ((R : Subgroup H).map H.subtype).map σ.toMonoidHom := by
  rw [sylowMapMulAut, Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem le_of_maxSylowCase {p : ℕ} (hp : p.Prime) (P : Sylow p G) {M : Subgroup G}
    (hWM : GLBWeakCore p (P : Subgroup G) ≤ M)
    (hcase : ∀ H : Subgroup G, GLBIsMaxTwoLocal H → ∀ R : Sylow p H,
      (R : Subgroup H).map H.subtype ≤ P → 3 ≤ pRank p ((R : Subgroup H).map H.subtype) →
        H ≤ M)
    {H : Subgroup G} (hH : IsTwoLocal H) (hHM : 3 ≤ pRank p (H ⊓ M)) : H ≤ M := by
  have : Fact p.Prime := ⟨hp⟩
  have hPrank : 3 ≤ pRank p (P : Subgroup G) := by
    rw [pRank_sylow_eq_globalRank p hp P]
    exact hHM.trans (pRank_mono p hp le_top)
  have hPM : (P : Subgroup G) ≤ M := (subgroup_le_weakCore_of_rank p hp _ hPrank).trans hWM
  obtain ⟨K, hHK, hK⟩ := exists_maximal_twoLocal hH
  have hKM : 3 ≤ pRank p (K ⊓ M) := hHM.trans (pRank_mono p hp (inf_le_inf_right M hHK))
  obtain ⟨R, hRM, hRrank, -⟩ := intersecting_local_has_contained_sylow p hp P hPM hWM hKM
  obtain ⟨m, hm⟩ := exists_conjugate_le_sylow_of_le p P hPM hRM (R.isPGroup'.map K.subtype)
  have hσ := glbIsMaxTwoLocal_map_mulAut hK (MulAut.conj (m : G))
  refine hHK.trans (le_of_map_conj_le m.2 (hcase _ hσ (sylowMapMulAut R _) ?_ ?_))
  · rw [map_subtype_sylowMapMulAut]
    exact hm
  · rw [map_subtype_sylowMapMulAut, pRank_map_of_injective p hp _ (MulEquiv.injective _)]
    exact hRrank

theorem d1_of_maxCase (hmax : D1MaxCase) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : CFSG.Open.IsKProper G)
    (hchar : CFSG.Open.IsCharTwoType G) (he : 4 ≤ CFSG.Open.evenRank G)
    (hpre : CFSG.Open.GLBPreuniqueness G) (p : ℕ) (hp : p ∈ CFSG.Open.GLBBetaFour G)
    (P : Sylow p G) (M : Subgroup G) (hM : CFSG.Open.GLBIsMaxTwoLocal M)
    (hWM : CFSG.Open.GLBWeakCore p (P : Subgroup G) ≤ M) (H : Subgroup G)
    (hH : CFSG.Open.IsTwoLocal H) (hHM : 3 ≤ CFSG.Open.pRank p (H ⊓ M)) : H ≤ M :=
  le_of_maxSylowCase hp.1 P hWM
    (hmax G ⟨inferInstance, hnonab, hK, hchar, he, hpre⟩ p P M ⟨hp, hM, hWM⟩) hH hHM

end CFSG.AGLEmbedding
