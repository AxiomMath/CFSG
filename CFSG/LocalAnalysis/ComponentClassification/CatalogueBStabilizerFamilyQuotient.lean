module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBStabilizerFamilyNormalizer
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

namespace CFSG.ComponentClassification.CatalogueBStabilizerFamily

universe u v

variable {G : Type u} [Group G] {X : Type v}

@[expose] def familyInner (rho : G →* Equiv.Perm X) : Subgroup (familyAut rho) :=
  (MulAut.conj : G →* MulAut G).range.subgroupOf (familyAut rho)

@[expose] def normalizerImage (rho : G →* Equiv.Perm X) : Subgroup (imageNormalizer rho) :=
  rho.range.subgroupOf (imageNormalizer rho)

instance familyInnerNormal (rho : G →* Equiv.Perm X) : (familyInner rho).Normal := by
  constructor
  intro alpha halpha beta
  obtain ⟨g, hg⟩ := halpha
  change MulAut.conj g = alpha.val at hg
  refine ⟨beta.val g, ?_⟩
  ext h
  change beta.val g * h * (beta.val g)⁻¹ =
    beta.val (alpha.val (beta.val.symm h))
  rw [← hg]
  simp

instance normalizerImageNormal (rho : G →* Equiv.Perm X) : (normalizerImage rho).Normal :=
  Subgroup.normal_in_normalizer

theorem familyInner_map_subtype (rho : G →* Equiv.Perm X) :
    (familyInner rho).map (familyAut rho).subtype = (MulAut.conj : G →* MulAut G).range :=
  Subgroup.map_subgroupOf_eq_of_le (inner_le_familyAut rho)

theorem normalizerImage_map_subtype (rho : G →* Equiv.Perm X) :
    (normalizerImage rho).map (imageNormalizer rho).subtype = rho.range :=
  Subgroup.map_subgroupOf_eq_of_le (range_le_imageNormalizer rho)

theorem normalizerEquiv_conj (rho : G →* Equiv.Perm X)
    (hrho : Function.Injective rho) (hs : Function.Injective (pointStabilizer rho)) (g : G) :
    (normalizerEquiv rho hrho hs ⟨MulAut.conj g, conj_mem_familyAut rho g⟩).val = rho g :=
  pointPerm_conj rho hs g

theorem normalizerEquiv_inner_image (rho : G →* Equiv.Perm X)
    (hrho : Function.Injective rho) (hs : Function.Injective (pointStabilizer rho)) :
    (familyInner rho).map (normalizerEquiv rho hrho hs).toMonoidHom = normalizerImage rho := by
  ext phi
  constructor
  · rintro ⟨alpha, ha, rfl⟩
    obtain ⟨g, hg⟩ := ha
    have halpha : alpha = ⟨MulAut.conj g, conj_mem_familyAut rho g⟩ := Subtype.ext hg.symm
    change (normalizerEquiv rho hrho hs alpha).val ∈ rho.range
    rw [halpha, normalizerEquiv_conj]
    exact ⟨g, rfl⟩
  · intro hphi
    obtain ⟨g, hg⟩ := hphi
    refine ⟨⟨MulAut.conj g, conj_mem_familyAut rho g⟩, ⟨g, rfl⟩, ?_⟩
    apply Subtype.ext
    exact (normalizerEquiv_conj rho hrho hs g).trans hg

abbrev familyOuter (rho : G →* Equiv.Perm X) :=
  familyAut rho ⧸ familyInner rho

abbrev normalizerOuter (rho : G →* Equiv.Perm X) :=
  imageNormalizer rho ⧸ normalizerImage rho

@[expose] noncomputable def quotientEquiv (rho : G →* Equiv.Perm X)
    (hrho : Function.Injective rho) (hs : Function.Injective (pointStabilizer rho)) :
    familyOuter rho ≃* normalizerOuter rho :=
  QuotientGroup.congr (familyInner rho) (normalizerImage rho)
    (normalizerEquiv rho hrho hs) (normalizerEquiv_inner_image rho hrho hs)

theorem quotientEquiv_mk (rho : G →* Equiv.Perm X)
    (hrho : Function.Injective rho) (hs : Function.Injective (pointStabilizer rho))
    (alpha : familyAut rho) :
    quotientEquiv rho hrho hs ((QuotientGroup.mk' (familyInner rho)) alpha) =
      (QuotientGroup.mk' (normalizerImage rho)) (normalizerEquiv rho hrho hs alpha) :=
  QuotientGroup.congr_mk' (familyInner rho) (normalizerImage rho)
    (normalizerEquiv rho hrho hs) (normalizerEquiv_inner_image rho hrho hs) alpha

end CFSG.ComponentClassification.CatalogueBStabilizerFamily
