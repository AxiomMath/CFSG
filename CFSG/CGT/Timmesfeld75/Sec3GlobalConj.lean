module

public import CFSG.CGT.Timmesfeld75.Sec3Iso
public import CFSG.CGT.Timmesfeld75.Sec5Basic

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups

section Generic

variable {G : Type*} [Group G]

theorem conjSubgroup_conjSubgroup_eq_conj (c g : G) (T : Subgroup G) :
    conjSubgroup g (conjSubgroup c T) = conjSubgroup c (conjSubgroup (c⁻¹ * g * c) T) := by
  rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
  congr 1
  group

theorem exists_normal_quotientEquiv_conj {X M : Subgroup G} (hN : (M.subgroupOf X).Normal)
    (c : G) {X' M' : Subgroup G} (hX : X' = conjSubgroup c X) (hM : M' = conjSubgroup c M) :
    ∃ _ : (M'.subgroupOf X').Normal,
      Nonempty (↥X' ⧸ M'.subgroupOf X' ≃* ↥X ⧸ M.subgroupOf X) := by
  subst hX hM
  have := hN
  let e : ↥X ≃* ↥(conjSubgroup c X) := MulEquiv.subgroupMap (MulAut.conj c) X
  have hcoe : ∀ z : ↥X, ((e z : ↥(conjSubgroup c X)) : G) = c * z * c⁻¹ := fun z =>
    (MulEquiv.coe_subgroupMap_apply (MulAut.conj c) X z).trans (MulAut.conj_apply c z)
  have hcoe' : ∀ y : ↥(conjSubgroup c X), ((e.symm y : ↥X) : G) = c⁻¹ * y * c := fun y => by
    have h1 := congrArg Subtype.val (e.apply_symm_apply y)
    rw [hcoe] at h1
    rw [← h1]
    group
  have he : (M.subgroupOf X).map e.toMonoidHom =
      (conjSubgroup c M).subgroupOf (conjSubgroup c X) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : (z : G) ∈ M := hz
      show ((e z : ↥(conjSubgroup c X)) : G) ∈ conjSubgroup c M
      rw [hcoe, mem_conjSubgroup]
      simpa [mul_assoc] using hz'
    · intro hy
      have hy' : (y : G) ∈ conjSubgroup c M := hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      show ((e.symm y : ↥X) : G) ∈ M
      rw [hcoe']
      exact mem_conjSubgroup.1 hy'
  have hN' : ((conjSubgroup c M).subgroupOf (conjSubgroup c X)).Normal :=
    he ▸ Subgroup.Normal.map hN e.toMonoidHom e.surjective
  exact ⟨hN', ⟨(QuotientGroup.congr _ _ e he).symm⟩⟩

end Generic

section Conj

variable {G : Type} [Group G]

theorem Sec3Global.conj {T : Subgroup G} (h : Sec3Global T) (c : G) :
    Sec3Global (conjSubgroup c T) := by
  intro g hne hL
  have e := conjSubgroup_conjSubgroup_eq_conj c g T
  have hne' : conjSubgroup (c⁻¹ * g * c) T ≠ T := fun h' => hne (by rw [e, h'])
  have hL' : normIn T (conjSubgroup (c⁻¹ * g * c) T) ≠ ⊥ := fun h' =>
    hL (by rw [e, normIn_conj, h', conjSubgroup_bot])
  have := (h _ hne' hL').conj_gen c
  rwa [← e] at this

theorem Sec3Iso.conj {A B : Subgroup G} (h : Sec3Iso A B) (c : G) :
    Sec3Iso (conjSubgroup c A) (conjSubgroup c B) := by
  obtain ⟨hN, f, hf, ⟨iso⟩⟩ := h
  obtain ⟨hN', ⟨e⟩⟩ := exists_normal_quotientEquiv_conj hN c
    (X' := conjSubgroup c A ⊔ conjSubgroup c B) (M' := cfgM (conjSubgroup c A) (conjSubgroup c B))
    (conjSubgroup_sup_eq_sup c A B).symm (cfgM_conj c A B)
  exact ⟨hN', f, hf, ⟨e.trans iso⟩⟩

theorem Sec3IsoGlobal.conj {T : Subgroup G} (h : Sec3IsoGlobal T) (c : G) :
    Sec3IsoGlobal (conjSubgroup c T) := by
  intro g hne hL
  have e := conjSubgroup_conjSubgroup_eq_conj c g T
  have hne' : conjSubgroup (c⁻¹ * g * c) T ≠ T := fun h' => hne (by rw [e, h'])
  have hL' : normIn T (conjSubgroup (c⁻¹ * g * c) T) ≠ ⊥ := fun h' =>
    hL (by rw [e, normIn_conj, h', conjSubgroup_bot])
  have := (h _ hne' hL').conj c
  rwa [← e] at this

end Conj

end CFSG.CGT.Timmesfeld75
