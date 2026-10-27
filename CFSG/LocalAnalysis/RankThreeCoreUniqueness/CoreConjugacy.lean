module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoreEmbedding

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type*} [Group G]

theorem centralizer_map_automorphism (subgroup : Subgroup G) (automorphism : MulAut G) :
    (Subgroup.centralizer (subgroup : Set G)).map automorphism.toMonoidHom =
      Subgroup.centralizer (subgroup.map automorphism.toMonoidHom : Set G) := by
  ext element
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hcentralizing
    apply Subgroup.mem_centralizer_iff.mpr
    rintro imageElement ⟨source, hsource, rfl⟩
    apply automorphism.symm.injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
      Subgroup.mem_centralizer_iff.mp hcentralizing source hsource
  · intro hcentralizing
    apply Subgroup.mem_centralizer_iff.mpr
    intro source hsource
    apply automorphism.injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using
      Subgroup.mem_centralizer_iff.mp hcentralizing (automorphism source)
        (Subgroup.mem_map_of_mem automorphism.toMonoidHom hsource)

theorem aschProduct_map_automorphism (ambient generator : Subgroup G) (automorphism : MulAut G) :
    (generator ⊔ (ambient ⊓ Subgroup.centralizer (generator : Set G))).map
        automorphism.toMonoidHom =
      generator.map automorphism.toMonoidHom ⊔
        (ambient.map automorphism.toMonoidHom ⊓
          Subgroup.centralizer (generator.map automorphism.toMonoidHom : Set G)) := by
  rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ automorphism.injective,
    centralizer_map_automorphism]

theorem map_automorphism_symm_map (subgroup : Subgroup G) (automorphism : MulAut G) :
    (subgroup.map automorphism.toMonoidHom).map automorphism.symm.toMonoidHom = subgroup := by
  rw [Subgroup.map_equiv_eq_comap_symm']
  exact Subgroup.comap_map_eq_self_of_injective automorphism.injective subgroup

theorem twoLocal_map_automorphism (localGroup : Subgroup G) (hlocal : IsTwoLocal localGroup)
    (automorphism : MulAut G) : IsTwoLocal (localGroup.map automorphism.toMonoidHom) := by
  obtain ⟨twoGroup, hnontrivial, hpGroup, hnormalizer⟩ := hlocal
  refine ⟨twoGroup.map automorphism.toMonoidHom, ?_, hpGroup.map automorphism.toMonoidHom, ?_⟩
  · intro htrivial
    apply hnontrivial
    apply Subgroup.map_injective (f := automorphism.toMonoidHom) automorphism.injective
    simpa only [Subgroup.map_bot] using htrivial
  · rw [hnormalizer, Subgroup.map_equiv_normalizer_eq]

variable [Finite G]

theorem pRank_map_automorphism (prime : ℕ) (hprime : 1 < prime)
    (subgroup : Subgroup G) (automorphism : MulAut G) :
    pRank prime (subgroup.map automorphism.toMonoidHom) = pRank prime subgroup := by
  exact (pRank_eq_of_subgroup_equiv prime hprime subgroup _
    (subgroup.equivMapOfInjective automorphism.toMonoidHom automorphism.injective)).symm

theorem aschCore_map_automorphism_le (threshold prime : ℕ) (hprime : 1 < prime)
    (ambient : Subgroup G) (automorphism : MulAut G) :
    (rankThreeAschCore threshold prime ambient).map automorphism.toMonoidHom ≤
      rankThreeAschCore threshold prime (ambient.map automorphism.toMonoidHom) := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply (aschCore_le_iff threshold prime ambient _).mpr
  intro generator hinclusion hrank hproductRank
  apply Subgroup.map_le_iff_le_comap.mp
  rw [Subgroup.map_equiv_normalizer_eq]
  apply aschCore_normalizer_le threshold prime _ (generator.map automorphism.toMonoidHom)
    (Subgroup.map_mono hinclusion)
  · rwa [pRank_map_automorphism prime hprime]
  · rw [← aschProduct_map_automorphism, pRank_map_automorphism prime hprime]
    exact hproductRank

theorem aschCore_map_automorphism (threshold prime : ℕ) (hprime : 1 < prime)
    (ambient : Subgroup G) (automorphism : MulAut G) :
    (rankThreeAschCore threshold prime ambient).map automorphism.toMonoidHom =
      rankThreeAschCore threshold prime (ambient.map automorphism.toMonoidHom) := by
  apply le_antisymm (aschCore_map_automorphism_le threshold prime hprime ambient automorphism)
  apply (Subgroup.map_le_map_iff_of_injective (f := automorphism.symm.toMonoidHom)
    automorphism.symm.injective).mp
  rw [map_automorphism_symm_map]
  have hinverse := aschCore_map_automorphism_le threshold prime hprime
    (ambient.map automorphism.toMonoidHom) automorphism.symm
  rwa [map_automorphism_symm_map] at hinverse

theorem aschCoreLocal_iff_one_sylow_per_prime (threshold : ℕ) :
    rankThreeAschCoreLocal G threshold ↔
      ∀ prime ∈ rankThreeSigmaA G, ∃ sylowGroup : Sylow prime G,
        ∃ localGroup : Subgroup G, IsTwoLocal localGroup ∧
          rankThreeAschCore threshold prime (sylowGroup : Subgroup G) ≤ localGroup := by
  constructor
  · intro hlocal prime hselected
    obtain ⟨localGroup, htwoLocal, hcore⟩ := hlocal prime hselected (default : Sylow prime G)
    exact ⟨default, localGroup, htwoLocal, hcore⟩
  · intro hwitness prime hselected targetSylow
    let : Fact prime.Prime := ⟨sigmaA_prime prime hselected⟩
    obtain ⟨sourceSylow, localGroup, hlocal, hcore⟩ := hwitness prime hselected
    obtain ⟨conjugator, hconjugator⟩ := MulAction.IsPretransitive.exists_smul_eq (M := G)
      sourceSylow targetSylow
    refine ⟨localGroup.map (MulAut.conj conjugator).toMonoidHom,
      twoLocal_map_automorphism localGroup hlocal (MulAut.conj conjugator), ?_⟩
    have himage := Subgroup.map_mono (f := (MulAut.conj conjugator).toMonoidHom) hcore
    rw [aschCore_map_automorphism threshold prime (sigmaA_prime prime hselected).one_lt,
      ← sylow_conjugate_eq_map, hconjugator] at himage
    exact himage

end CFSG.RankThreeCoreUniqueness.Helpers
