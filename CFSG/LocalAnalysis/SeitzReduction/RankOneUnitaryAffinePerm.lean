module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneStageTransport
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis
open scoped LinearAlgebra.Projectivization CFSG.SeitzReduction.RankOne.DegreeEight

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Defs

variable {Ω : Type*}

@[expose] def HasRegularNormalSubgroup (N : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∃ E : Subgroup (Equiv.Perm Ω), E ≤ N ∧ (E.subgroupOf N).Normal ∧
    ∀ a b : Ω, ∃! x : E, (x : Equiv.Perm Ω) a = b

@[expose] def IsProjectiveEight (N : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∃ β : Ω ≃ ℙ (ZMod 7) (Fin 2 → ZMod 7), ∀ σ : Equiv.Perm Ω,
    σ ∈ N ↔ ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7), ∀ Q, β (σ Q) = g • β Q

end Defs

@[expose] def NonabelianSimpleNormalCatalog {Ω : Type} (N : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ S : Subgroup (Equiv.Perm Ω), S ≤ N → (S.subgroupOf N).Normal → IsSimpleGroup S →
    (∃ a b : S, a * b ≠ b * a) → CFSG.Blueprint.Catalog S

theorem gmsHasRegularNormal_iff {D : Type*} [Group D] (U R : Subgroup D) :
    GMSHasRegularNormal U R ↔
      HasRegularNormalSubgroup (gmsRootConjugateAction (U ⊔ R) R).range :=
  Iff.rfl

theorem gmsProjectiveEight_iff {D : Type*} [Group D] (U R : Subgroup D) :
    GMSProjectiveEight U R ↔ IsProjectiveEight (gmsRootConjugateAction (U ⊔ R) R).range :=
  Iff.rfl

section Transport

variable {Ω Ω' : Type*} (e : Ω ≃ Ω')

theorem permCongrHom_apply_apply (σ : Equiv.Perm Ω) (a : Ω') :
    (e.permCongrHom σ : Equiv.Perm Ω') a = e (σ (e.symm a)) :=
  rfl

theorem HasRegularNormalSubgroup.map_permCongr {N : Subgroup (Equiv.Perm Ω)}
    (h : HasRegularNormalSubgroup N) :
    HasRegularNormalSubgroup (N.map e.permCongrHom.toMonoidHom) := by
  obtain ⟨E, hEN, hEn, hreg⟩ := h
  refine ⟨E.map e.permCongrHom.toMonoidHom, map_mono hEN,
    normal_subgroupOf_map_equiv e.permCongrHom hEN hEn, fun a b => ?_⟩
  obtain ⟨x, hx, hxu⟩ := hreg (e.symm a) (e.symm b)
  refine ⟨⟨e.permCongrHom x, mem_map_of_mem _ x.2⟩, ?_, ?_⟩
  · change e ((x : Equiv.Perm Ω) (e.symm a)) = b
    rw [hx, Equiv.apply_symm_apply]
  · rintro ⟨y, hy⟩ hya
    obtain ⟨z, hz, rfl⟩ := mem_map.mp hy
    have hza : z (e.symm a) = e.symm b := by
      have h1 : e (z (e.symm a)) = b := hya
      rw [← h1, Equiv.symm_apply_apply]
    have hzx := hxu ⟨z, hz⟩ hza
    apply Subtype.ext
    change e.permCongrHom z = e.permCongrHom x
    rw [show z = (x : Equiv.Perm Ω) from congrArg Subtype.val hzx]

theorem IsProjectiveEight.map_permCongr {N : Subgroup (Equiv.Perm Ω)}
    (h : IsProjectiveEight N) : IsProjectiveEight (N.map e.permCongrHom.toMonoidHom) := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨e.symm.trans β, fun σ => ?_⟩
  have hmem : σ ∈ N.map e.permCongrHom.toMonoidHom ↔ e.permCongrHom.symm σ ∈ N := by
    rw [mem_map_equiv]
  rw [hmem, hβ]
  refine exists_congr fun g => ⟨fun hg Q => ?_, fun hg Q => ?_⟩
  · have h1 := hg (e.symm Q)
    simpa [Equiv.permCongrHom, Equiv.permCongr_apply] using h1
  · have h1 := hg (e Q)
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply] at h1
    have h2 : (e.permCongrHom.symm σ : Equiv.Perm Ω) Q = e.symm (σ (e Q)) := rfl
    rw [h2]
    exact h1

end Transport

theorem NonabelianSimpleNormalCatalog.of_map_permCongr {Ω Ω' : Type} (e : Ω ≃ Ω')
    {N : Subgroup (Equiv.Perm Ω)}
    (h : NonabelianSimpleNormalCatalog (N.map e.permCongrHom.toMonoidHom)) :
    NonabelianSimpleNormalCatalog N := by
  intro S hSN hSn hs hnab
  have hiso : S ≃* S.map e.permCongrHom.toMonoidHom :=
    S.equivMapOfInjective _ e.permCongrHom.injective
  refine CFSG.SectionRank.catalog_of_mulEquiv hiso (h _ (map_mono hSN)
    (normal_subgroupOf_map_equiv e.permCongrHom hSN hSn) hiso.symm.isSimpleGroup ?_)
  obtain ⟨a, b, hab⟩ := hnab
  refine ⟨hiso a, hiso b, fun h1 => hab ?_⟩
  apply hiso.injective
  rw [map_mul, map_mul, h1]

theorem map_permCongrHom_symm_map {Ω Ω' : Type*} (e : Ω ≃ Ω') (N : Subgroup (Equiv.Perm Ω)) :
    (N.map e.permCongrHom.toMonoidHom).map e.symm.permCongrHom.toMonoidHom = N := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id N
  ext σ x
  simp [Equiv.permCongrHom, Equiv.permCongr_apply]

end CFSG.SeitzReduction.RankOne
