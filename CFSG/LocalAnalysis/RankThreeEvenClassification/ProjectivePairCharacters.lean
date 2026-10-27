module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SemisimpleProjectivePairs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.EigenlineCharacters

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem projective_plane_pointwise_pair_embeds_units {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space] [FiniteDimensional field space]
    (hdimension : Module.finrank field space = 2)
    (subgroup : Subgroup (space ≃ₗ[field] space))
    (projectiveSubgroup : Subgroup ((linearProjectiveAction field space).comp subgroup.subtype).range)
    (first second : Projectivization field space) (hne : first ≠ second)
    (hfixed : ∀ member : projectiveSubgroup,
      (member : Equiv.Perm (Projectivization field space)) first = first ∧
        (member : Equiv.Perm (Projectivization field space)) second = second) :
    ∃ character : projectiveSubgroup →* fieldˣ, Function.Injective character := by
  classical
  let projectiveAction := (linearProjectiveAction field space).comp subgroup.subtype
  let liftSubgroup := projectiveSubgroup.comap projectiveAction.rangeRestrict
  let projection : liftSubgroup →* projectiveSubgroup :=
    (projectiveAction.rangeRestrict.comp liftSubgroup.subtype).codRestrict projectiveSubgroup
      (fun member => member.property)
  let linearAction : liftSubgroup →* (space ≃ₗ[field] space) :=
    subgroup.subtype.comp liftSubgroup.subtype
  have hprojectionSurjective : Function.Surjective projection := by
    intro member
    obtain ⟨preimage, hpreimage⟩ := projectiveAction.rangeRestrict_surjective (member : projectiveAction.range)
    have hmem : preimage ∈ liftSubgroup := by
      change projectiveAction.rangeRestrict preimage ∈ projectiveSubgroup
      rw [hpreimage]
      exact member.property
    refine ⟨⟨preimage, hmem⟩, ?_⟩
    exact Subtype.ext hpreimage
  have hprojectiveEq : ∀ member : liftSubgroup,
      linearProjectiveAction field space (linearAction member) =
        (projection member : Equiv.Perm (Projectivization field space)) := fun _ => rfl
  have hfirstScalar : ∀ member : liftSubgroup,
      ∃ scalar : field, linearAction member first.rep = scalar • first.rep := by
    intro member
    apply (projective_fixed_point_iff_eigenvector (linearAction member) first.rep first.rep_nonzero).mp
    simpa only [Projectivization.mk_rep, hprojectiveEq] using (hfixed (projection member)).1
  have hsecondScalar : ∀ member : liftSubgroup,
      ∃ scalar : field, linearAction member second.rep = scalar • second.rep := by
    intro member
    apply (projective_fixed_point_iff_eigenvector (linearAction member) second.rep second.rep_nonzero).mp
    simpa only [Projectivization.mk_rep, hprojectiveEq] using (hfixed (projection member)).2
  obtain ⟨firstCharacter, hfirstCharacter⟩ :=
    invariant_eigenline_has_character linearAction first.rep first.rep_nonzero hfirstScalar
  obtain ⟨secondCharacter, hsecondCharacter⟩ :=
    invariant_eigenline_has_character linearAction second.rep second.rep_nonzero hsecondScalar
  let ratio := firstCharacter / secondCharacter
  have hindependent := (LinearIndependent.pair_iff.mp
    (distinct_projective_representatives_independent first second hne))
  have hspan := distinct_projective_plane_representatives_span hdimension first second hne
  have hkernel : projection.ker = ratio.ker := by
    ext member
    simp only [MonoidHom.mem_ker]
    constructor
    · intro hidentity
      have hprojectiveIdentity : linearProjectiveAction field space (linearAction member) = 1 := by
        rw [hprojectiveEq, hidentity]
        rfl
      have hscalars := projective_identity_eigenbasis_scalars_eq (linearAction member)
        hprojectiveIdentity first.rep second.rep (firstCharacter member : field)
        (secondCharacter member : field) (hfirstCharacter member) (hsecondCharacter member) hindependent
      change firstCharacter member / secondCharacter member = 1
      exact div_eq_one.mpr (Units.ext hscalars)
    · intro hratio
      have hcharacters : firstCharacter member = secondCharacter member := div_eq_one.mp hratio
      have hscalar : ∀ vector : space,
          linearAction member vector = (firstCharacter member : field) • vector := by
        intro vector
        obtain ⟨firstCoefficient, secondCoefficient, rfl⟩ := hspan vector
        rw [map_add, map_smul, map_smul, hfirstCharacter, hsecondCharacter, ← hcharacters,
          smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
        congr 1 <;> congr 1 <;> ring
      have hprojectiveIdentity := scalar_linear_projectiveAction_eq_one (linearAction member)
        (firstCharacter member : field) hscalar
      apply Subtype.ext
      apply Subtype.ext
      exact (hprojectiveEq member).symm.trans hprojectiveIdentity
  obtain ⟨inverse, hinverse⟩ := hprojectionSurjective.hasRightInverse
  let character : projectiveSubgroup →* fieldˣ :=
    projection.liftOfRightInverse inverse hinverse ⟨ratio, hkernel.le⟩
  have hcharacter : ∀ member : liftSubgroup, character (projection member) = ratio member :=
    MonoidHom.liftOfRightInverse_comp_apply projection inverse hinverse ⟨ratio, hkernel.le⟩
  refine ⟨character, (MonoidHom.ker_eq_bot_iff character).mp ?_⟩
  apply le_antisymm
  · intro member hmember
    obtain ⟨preimage, rfl⟩ := hprojectionSurjective member
    have hratio : preimage ∈ ratio.ker := by
      change ratio preimage = 1
      exact (hcharacter preimage).symm.trans hmember
    have hprojection : projection preimage = 1 := by
      change preimage ∈ projection.ker
      rw [hkernel]
      exact hratio
    exact Subgroup.mem_bot.mpr hprojection
  · exact bot_le

end CFSG.RankThreeEvenClassification.Helpers
