module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.GeneratedCore

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem subgroup_map_equiv_symm {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] (equivalence : G ≃* otherGroup) (subgroup : Subgroup G) :
    (subgroup.map equivalence.toMonoidHom).map equivalence.symm.toMonoidHom = subgroup := by
  have hcomposition : equivalence.symm.toMonoidHom.comp equivalence.toMonoidHom =
      MonoidHom.id G := by
    ext element
    exact equivalence.symm_apply_apply element
  rw [Subgroup.map_map, hcomposition, Subgroup.map_id]

theorem centralizer_map_equiv {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] (equivalence : G ≃* otherGroup) (subgroup : Subgroup G) :
    (Subgroup.centralizer (subgroup : Set G)).map equivalence.toMonoidHom =
      Subgroup.centralizer (subgroup.map equivalence.toMonoidHom : Set otherGroup) := by
  ext element
  constructor
  · intro hmem
    obtain ⟨preimage, hpreimage, rfl⟩ := Subgroup.mem_map.mp hmem
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    obtain ⟨otherPreimage, hotherPreimage, rfl⟩ := Subgroup.mem_map.mp hother
    rw [← map_mul, ← map_mul]
    exact congrArg equivalence (Subgroup.mem_centralizer_iff.mp hpreimage
      otherPreimage hotherPreimage)
  · intro hmem
    apply Subgroup.mem_map.mpr
    refine ⟨equivalence.symm element, ?_, equivalence.apply_symm_apply element⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    apply equivalence.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_centralizer_iff.mp hmem (equivalence other)
      (Subgroup.mem_map_of_mem equivalence.toMonoidHom hother)

theorem relativeCentralizer_map_equiv {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] (equivalence : G ≃* otherGroup)
    (overgroup subgroup : Subgroup G) :
    (relativeCentralizer overgroup subgroup).map equivalence.toMonoidHom =
      relativeCentralizer (overgroup.map equivalence.toMonoidHom)
        (subgroup.map equivalence.toMonoidHom) := by
  rw [relativeCentralizer, Subgroup.map_inf _ _ _ equivalence.injective,
    centralizer_map_equiv]
  rfl

theorem centralizerProduct_map_equiv {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] (equivalence : G ≃* otherGroup)
    (overgroup subgroup : Subgroup G) :
    (centralizerProduct overgroup subgroup).map equivalence.toMonoidHom =
      centralizerProduct (overgroup.map equivalence.toMonoidHom)
        (subgroup.map equivalence.toMonoidHom) := by
  rw [centralizerProduct, Subgroup.map_sup, relativeCentralizer_map_equiv]
  rfl

theorem generatedPCore_map_le {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] [Finite G] [Finite otherGroup]
    (prime : ℕ) (hprime : prime.Prime) (threshold : ℕ)
    (equivalence : G ≃* otherGroup) (overgroup : Subgroup G) :
    (generatedPCore prime threshold overgroup).map equivalence.toMonoidHom ≤
      generatedPCore prime threshold (overgroup.map equivalence.toMonoidHom) := by
  unfold generatedPCore
  simp only [Subgroup.map_iSup]
  refine iSup_le fun subgroup => iSup_le fun hle => iSup_le fun hrank => ?_
  rw [Subgroup.map_equiv_normalizer_eq]
  apply normalizer_le_generatedPCore prime threshold (overgroup.map equivalence.toMonoidHom)
    (subgroup.map equivalence.toMonoidHom) (Subgroup.map_mono hle)
  simpa only [pRank_map_equiv prime hprime] using hrank

theorem generatedPCore_map_equiv {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] [Finite G] [Finite otherGroup]
    (prime : ℕ) (hprime : prime.Prime) (threshold : ℕ)
    (equivalence : G ≃* otherGroup) (overgroup : Subgroup G) :
    (generatedPCore prime threshold overgroup).map equivalence.toMonoidHom =
      generatedPCore prime threshold (overgroup.map equivalence.toMonoidHom) := by
  apply le_antisymm (generatedPCore_map_le prime hprime threshold equivalence overgroup)
  apply (Subgroup.map_le_map_iff_of_injective
    (f := equivalence.symm.toMonoidHom) equivalence.symm.injective).mp
  rw [subgroup_map_equiv_symm]
  have hreverse := generatedPCore_map_le prime hprime threshold equivalence.symm
    (overgroup.map equivalence.toMonoidHom)
  simpa only [subgroup_map_equiv_symm] using hreverse

theorem aschbacherCore_map_le {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] [Finite G] [Finite otherGroup]
    (prime : ℕ) (hprime : prime.Prime) (threshold : ℕ)
    (equivalence : G ≃* otherGroup) (overgroup : Subgroup G) :
    (aschbacherCore prime threshold overgroup).map equivalence.toMonoidHom ≤
      aschbacherCore prime threshold (overgroup.map equivalence.toMonoidHom) := by
  unfold aschbacherCore
  simp only [Subgroup.map_iSup]
  refine iSup_le fun subgroup => iSup_le fun hle => iSup_le fun hrank =>
    iSup_le fun hproduct => ?_
  rw [Subgroup.map_equiv_normalizer_eq]
  apply normalizer_le_aschbacherCore prime threshold (overgroup.map equivalence.toMonoidHom)
    (subgroup.map equivalence.toMonoidHom) (Subgroup.map_mono hle)
  · simpa only [pRank_map_equiv prime hprime] using hrank
  · rw [← centralizerProduct_map_equiv, pRank_map_equiv prime hprime]
    exact hproduct

theorem aschbacherCore_map_equiv {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] [Finite G] [Finite otherGroup]
    (prime : ℕ) (hprime : prime.Prime) (threshold : ℕ)
    (equivalence : G ≃* otherGroup) (overgroup : Subgroup G) :
    (aschbacherCore prime threshold overgroup).map equivalence.toMonoidHom =
      aschbacherCore prime threshold (overgroup.map equivalence.toMonoidHom) := by
  apply le_antisymm (aschbacherCore_map_le prime hprime threshold equivalence overgroup)
  apply (Subgroup.map_le_map_iff_of_injective
    (f := equivalence.symm.toMonoidHom) equivalence.symm.injective).mp
  rw [subgroup_map_equiv_symm]
  have hreverse := aschbacherCore_map_le prime hprime threshold equivalence.symm
    (overgroup.map equivalence.toMonoidHom)
  simpa only [subgroup_map_equiv_symm] using hreverse

theorem isTwoLocal_map_equiv {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] (equivalence : G ≃* otherGroup)
    (subgroup : Subgroup G) (hlocal : IsTwoLocal subgroup) :
    IsTwoLocal (subgroup.map equivalence.toMonoidHom) := by
  obtain ⟨twosubgroup, hnontrivial, hpgroup, heq⟩ := hlocal
  refine ⟨twosubgroup.map equivalence.toMonoidHom, ?_, ?_, ?_⟩
  · exact fun hbot => hnontrivial
      ((Subgroup.map_eq_bot_iff_of_injective twosubgroup equivalence.injective).mp hbot)
  · exact hpgroup.of_equiv (equivalence.subgroupMap twosubgroup)
  · rw [heq, Subgroup.map_equiv_normalizer_eq]

theorem aschbacherCore_smul {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (threshold : ℕ) (overgroup : Subgroup G) (element : G) :
    (MulAut.conj element) • aschbacherCore prime threshold overgroup =
      aschbacherCore prime threshold ((MulAut.conj element) • overgroup) := by
  exact aschbacherCore_map_equiv prime hprime threshold (MulAut.conj element) overgroup

theorem normalizer_le_normalizer_aschbacherCore {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (threshold : ℕ) (overgroup : Subgroup G) :
    Subgroup.normalizer (overgroup : Set G) ≤
      Subgroup.normalizer (aschbacherCore prime threshold overgroup : Set G) := by
  intro element hmem
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change (aschbacherCore prime threshold overgroup).map (MulAut.conj element).toMonoidHom = _
  rw [aschbacherCore_map_equiv prime hprime threshold]
  exact congrArg (aschbacherCore prime threshold)
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp hmem)

theorem core_local_one_sylow_iff {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (threshold : ℕ) (sylow : Sylow prime G) :
    (∃ localSubgroup : Subgroup G, IsTwoLocal localSubgroup ∧
      aschbacherCore prime threshold (sylow : Subgroup G) ≤ localSubgroup) ↔
    (∀ otherSylow : Sylow prime G, ∃ localSubgroup : Subgroup G, IsTwoLocal localSubgroup ∧
      aschbacherCore prime threshold (otherSylow : Subgroup G) ≤ localSubgroup) := by
  have : Fact prime.Prime := ⟨hprime⟩
  constructor
  · rintro ⟨localSubgroup, hlocal, hcore⟩ otherSylow
    obtain ⟨element, rfl⟩ := MulAction.exists_smul_eq G sylow otherSylow
    refine ⟨localSubgroup.map (MulAut.conj element).toMonoidHom,
      isTwoLocal_map_equiv (MulAut.conj element) localSubgroup hlocal, ?_⟩
    change aschbacherCore prime threshold ((MulAut.conj element) • (sylow : Subgroup G)) ≤ _
    rw [← aschbacherCore_smul prime hprime threshold]
    exact Subgroup.map_mono hcore
  · intro hlocal
    exact hlocal sylow

end CFSG.RankThreeEvenClassification.Helpers
