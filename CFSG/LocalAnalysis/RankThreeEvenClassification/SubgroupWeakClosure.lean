module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantConjugacy

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose] noncomputable def subgroupConjugateOrbit {G : Type u} [Group G]
    (actor seed : Subgroup G) : Subgroup G :=
  ⨆ member : actor, seed.map (MulAut.conj (member : G)).toMonoidHom

theorem subgroupConjugateOrbit_normalized {G : Type u} [Group G] (actor seed : Subgroup G) :
    actor ≤ Subgroup.normalizer (subgroupConjugateOrbit actor seed : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro member hmember element helement
  have hmapLe : (subgroupConjugateOrbit actor seed).map (MulAut.conj member).toMonoidHom ≤
      subgroupConjugateOrbit actor seed := by
    rw [subgroupConjugateOrbit, Subgroup.map_iSup]
    apply iSup_le
    intro actingMember
    rw [← subgroup_map_conj_mul]
    exact le_iSup (fun conjugator : actor => seed.map (MulAut.conj (conjugator : G)).toMonoidHom)
      (⟨member, hmember⟩ * actingMember)
  exact hmapLe (Subgroup.mem_map_of_mem (MulAut.conj member).toMonoidHom helement)

end CFSG.RankThreeEvenClassification.Helpers
