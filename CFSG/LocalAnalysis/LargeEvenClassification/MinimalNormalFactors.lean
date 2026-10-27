module

public import CFSG.LocalAnalysis.LargeEvenClassification.SubgroupTransport
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreSocle

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem minimal_normal_map_mulAut {Ambient : Type groupUniverse} [Group Ambient]
    (Normal : Subgroup Ambient) (hminimal : minimalNormalEligible Normal) (coordinates : MulAut Ambient) :
    minimalNormalEligible (Normal.map coordinates.toMonoidHom) := by
  let : Normal.Normal := hminimal.prop.1
  refine ⟨⟨Subgroup.Normal.map inferInstance coordinates.toMonoidHom coordinates.surjective, ?_⟩, ?_⟩
  · exact fun hzero => hminimal.prop.2
      ((Subgroup.map_eq_bot_iff_of_injective _ coordinates.injective).mp hzero)
  · intro Smaller hsmaller hle
    let : Smaller.Normal := hsmaller.1
    have hpreimageNormal : (Smaller.map coordinates.symm.toMonoidHom).Normal :=
      Subgroup.Normal.map inferInstance _ coordinates.symm.surjective
    have hpreimageNonzero : Smaller.map coordinates.symm.toMonoidHom ≠ ⊥ :=
      fun hzero => hsmaller.2 ((Subgroup.map_eq_bot_iff_of_injective _ coordinates.symm.injective).mp hzero)
    have hpreimageLe : Smaller.map coordinates.symm.toMonoidHom ≤ Normal := by
      have hmapped := Subgroup.map_mono (f := coordinates.symm.toMonoidHom) hle
      rwa [subgroup_map_inverse_mulEquiv] at hmapped
    have hminimalLe := hminimal.2 ⟨hpreimageNormal, hpreimageNonzero⟩ hpreimageLe
    have hmapped := Subgroup.map_mono (f := coordinates.toMonoidHom) hminimalLe
    rwa [subgroup_map_forward_inverse_mulEquiv] at hmapped

instance finiteSocle_characteristic (Ambient : Type groupUniverse) [Group Ambient] :
    (finiteSocle Ambient).Characteristic := by
  apply Subgroup.characteristic_iff_map_eq.mpr
  intro coordinates
  have hmapLe : ∀ automorphism : MulAut Ambient,
      (finiteSocle Ambient).map automorphism.toMonoidHom ≤ finiteSocle Ambient := by
    intro automorphism
    rw [finiteSocle, Subgroup.map_iSup]
    apply iSup_le
    intro Candidate
    exact minimal_normal_le_socle _ (minimal_normal_map_mulAut _ Candidate.property automorphism)
  apply le_antisymm (hmapLe coordinates)
  have hinverse := Subgroup.map_mono (f := coordinates.toMonoidHom) (hmapLe coordinates.symm)
  rwa [subgroup_map_forward_inverse_mulEquiv] at hinverse

theorem distinct_minimal_normals_disjoint {Ambient : Type groupUniverse} [Group Ambient]
    (First Second : Subgroup Ambient) (hfirst : minimalNormalEligible First)
    (hsecond : minimalNormalEligible Second) (hdistinct : First ≠ Second) : Disjoint First Second := by
  let : First.Normal := hfirst.prop.1
  let : Second.Normal := hsecond.prop.1
  apply disjoint_iff.mpr
  by_contra hnonzero
  have hfirstLe := hfirst.2 (show (First ⊓ Second).Normal ∧ (First ⊓ Second : Subgroup Ambient) ≠ ⊥ from
    ⟨inferInstance, hnonzero⟩) inf_le_left
  have hsecondLe := hsecond.2 (show (First ⊓ Second).Normal ∧ (First ⊓ Second : Subgroup Ambient) ≠ ⊥ from
    ⟨inferInstance, hnonzero⟩) inf_le_right
  exact hdistinct (le_antisymm (hfirstLe.trans inf_le_right) (hsecondLe.trans inf_le_left))

theorem socle_top_minimal_centralizer_generates {Ambient : Type groupUniverse} [Group Ambient]
    (hsocle : finiteSocle Ambient = ⊤) (Normal : Subgroup Ambient) (hminimal : minimalNormalEligible Normal) :
    Normal ⊔ Subgroup.centralizer (Normal : Set Ambient) = ⊤ := by
  let : Normal.Normal := hminimal.prop.1
  apply top_unique
  rw [← hsocle]
  apply iSup_le
  intro Candidate
  by_cases heq : Candidate.val = Normal
  · exact heq ▸ le_sup_left
  · let : Candidate.val.Normal := Candidate.property.prop.1
    have hdisjoint := distinct_minimal_normals_disjoint Candidate.val Normal Candidate.property hminimal heq
    have hcentralizes : Candidate.val ≤ Subgroup.centralizer (Normal : Set Ambient) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (Subgroup.commutator_eq_bot_of_disjoint hdisjoint)
    exact hcentralizes.trans le_sup_right

theorem socle_top_minimal_normal_simple {Ambient : Type groupUniverse} [Group Ambient]
    (hsocle : finiteSocle Ambient = ⊤) (Normal : Subgroup Ambient) (hminimal : minimalNormalEligible Normal) :
    IsSimpleGroup Normal := by
  let : Normal.Normal := hminimal.prop.1
  let : Nontrivial Normal := (Subgroup.nontrivial_iff_ne_bot _).mpr hminimal.prop.2
  apply IsSimpleGroup.mk
  intro Internal hinternalNormal
  let : Internal.Normal := hinternalNormal
  let Mapped := Internal.map Normal.subtype
  have hmappedLe : Mapped ≤ Normal := Subgroup.map_subtype_le _
  have hinternalEq : Mapped.subgroupOf Normal = Internal :=
    Subgroup.comap_map_eq_self_of_injective Normal.subtype_injective Internal
  have hnormalizes : Normal ≤ Subgroup.normalizer (Mapped : Set Ambient) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hmappedLe).mp
      (hinternalEq.symm ▸ hinternalNormal)
  have hcentralizesLe : Subgroup.centralizer (Normal : Set Ambient) ≤
      Subgroup.normalizer (Mapped : Set Ambient) :=
    (Subgroup.centralizer_le hmappedLe).trans (Subgroup.centralizer_le_normalizer _)
  have hmappedNormal : Mapped.Normal := Subgroup.normalizer_eq_top_iff.mp
    (top_unique ((socle_top_minimal_centralizer_generates hsocle Normal hminimal).symm ▸
      sup_le hnormalizes hcentralizesLe))
  by_cases hzero : Mapped = ⊥
  · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective _ Normal.subtype_injective).mp hzero)
  · have hnormalLe := hminimal.2 ⟨hmappedNormal, hzero⟩ hmappedLe
    apply Or.inr
    apply Subgroup.map_injective Normal.subtype_injective
    exact (le_antisymm hmappedLe hnormalLe).trans
      (Subgroup.range_subtype Normal).symm |>.trans (MonoidHom.range_eq_map _)

theorem socle_top_centerless_minimal_nonabelian {Ambient : Type groupUniverse} [Group Ambient]
    (hsocle : finiteSocle Ambient = ⊤) (hcenter : Subgroup.center Ambient = ⊥)
    (Normal : Subgroup Ambient) (hminimal : minimalNormalEligible Normal) :
    ∃ first second : Normal, first * second ≠ second * first := by
  by_contra hnot
  have hcommutative : IsMulCommutative Normal := by
    push Not at hnot
    exact ⟨⟨hnot⟩⟩
  have hnormalCentralizes : Normal ≤ Subgroup.centralizer (Normal : Set Ambient) := by
    intro element helement
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    exact congrArg (fun entry : Normal => entry.val)
      (@mul_comm' Normal _ hcommutative ⟨other, hother⟩ ⟨element, helement⟩)
  have hcentralizerTop : Subgroup.centralizer (Normal : Set Ambient) = ⊤ := by
    have hgenerates := socle_top_minimal_centralizer_generates hsocle Normal hminimal
    rwa [sup_eq_right.mpr hnormalCentralizes] at hgenerates
  have hleCenter : Normal ≤ Subgroup.center Ambient :=
    Subgroup.centralizer_eq_top_iff_subset.mp hcentralizerTop
  exact hminimal.prop.2 (le_antisymm (hcenter ▸ hleCenter) bot_le)

end CFSG.LargeEvenClassification.Helpers
