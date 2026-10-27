module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.SylowNormalizerControl

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G]
variable {A : Type*} [Group A] [MulDistribMulAction A G]

@[expose] def InvariantSubgroup (subgroup : Subgroup G) : Prop :=
  ∀ actor : A, ∀ element : G, element ∈ subgroup → actor • element ∈ subgroup

theorem coprime_pgroup_exists_invariant_sylow [Finite G] (actorPrime sylowPrime : ℕ)
    [Fact (Nat.Prime actorPrime)] [Fact (Nat.Prime sylowPrime)]
    (hpgroup : IsPGroup actorPrime A) (hcoprime : ¬ actorPrime ∣ Nat.card G) :
    ∃ sylow : Sylow sylowPrime G, InvariantSubgroup (A := A) (sylow : Subgroup G) := by
  classical
  let starting : Sylow sylowPrime G := Classical.choice inferInstance
  have hnotdvd : ¬ actorPrime ∣ Nat.card (Sylow sylowPrime G) := by
    intro hdiv
    exact hcoprime (hdiv.trans
      (starting.card_dvd_index.trans (starting : Subgroup G).index_dvd_card))
  obtain ⟨sylow, hfixed⟩ := hpgroup.nonempty_fixed_point_of_prime_not_dvd_card
    (Sylow sylowPrime G) hnotdvd
  refine ⟨sylow, ?_⟩
  intro actor element hmem
  have hsmul : actor • sylow = sylow := MulAction.mem_fixedPoints.mp hfixed actor
  have hmemsmul : actor • element ∈ ((actor • sylow : Sylow sylowPrime G) : Subgroup G) := by
    rw [Sylow.pointwise_smul_def]
    exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨element, hmem, rfl⟩
  rw [hsmul] at hmemsmul
  exact hmemsmul

@[expose, instance_reducible]
def invariantSubgroupAction (subgroup : Subgroup G)
    (hinvariant : InvariantSubgroup (A := A) subgroup) : MulDistribMulAction A subgroup where
  smul actor element := ⟨actor • element.val, hinvariant actor element.val element.property⟩
  one_smul element := Subtype.ext (one_smul A element.val)
  mul_smul first second element := Subtype.ext (mul_smul first second element.val)
  smul_mul actor first second := Subtype.ext (smul_mul' actor first.val second.val)
  smul_one actor := Subtype.ext (smul_one actor)

theorem invariant_subgroup_normalizer (subgroup : Subgroup G)
    (hinvariant : InvariantSubgroup (A := A) subgroup) :
    InvariantSubgroup (A := A) (Subgroup.normalizer (subgroup : Set G)) := by
  intro actor element hmem
  apply Subgroup.mem_normalizer_iff.mpr
  intro other
  constructor
  · intro hother
    have hpreimage := hinvariant actor⁻¹ other hother
    have hconj := (Subgroup.mem_normalizer_iff.mp hmem (actor⁻¹ • other)).mp hpreimage
    have himage := hinvariant actor _ hconj
    simpa only [smul_mul', smul_inv', smul_inv_smul] using himage
  · intro hconj
    have hpreimage := hinvariant actor⁻¹ _ hconj
    have hback : element * (actor⁻¹ • other) * element⁻¹ ∈ subgroup := by
      simpa only [smul_mul', smul_inv', inv_smul_smul] using hpreimage
    have hother := (Subgroup.mem_normalizer_iff.mp hmem (actor⁻¹ • other)).mpr hback
    simpa only [smul_inv_smul] using hinvariant actor _ hother

theorem coprime_pgroup_invariant_sylow_containment [Finite G]
    (actorPrime sylowPrime : ℕ) [Fact (Nat.Prime actorPrime)] [Fact (Nat.Prime sylowPrime)]
    (hpgroup : IsPGroup actorPrime A) (hcoprime : ¬ actorPrime ∣ Nat.card G)
    (subgroup : Subgroup G) (hsubgroupP : IsPGroup sylowPrime subgroup)
    (hsubgroupInvariant : InvariantSubgroup (A := A) subgroup) :
    ∃ sylow : Sylow sylowPrime G, subgroup ≤ (sylow : Subgroup G) ∧
      InvariantSubgroup (A := A) (sylow : Subgroup G) := by
  classical
  let candidates : Set (Subgroup G) :=
    {larger | subgroup ≤ larger ∧ IsPGroup sylowPrime larger ∧ InvariantSubgroup (A := A) larger}
  obtain ⟨maximal, hmaximal⟩ := candidates.toFinite.exists_maximal
    (show candidates.Nonempty from ⟨subgroup, le_rfl, hsubgroupP, hsubgroupInvariant⟩)
  obtain ⟨hsubgroupLe, hmaximalP, hmaximalInvariant⟩ := hmaximal.prop
  let normalizer : Subgroup G := Subgroup.normalizer (maximal : Set G)
  have hnormalizerInvariant : InvariantSubgroup (A := A) normalizer :=
    invariant_subgroup_normalizer maximal hmaximalInvariant
  let _ : MulDistribMulAction A normalizer :=
    invariantSubgroupAction normalizer hnormalizerInvariant
  have hnormalizerCoprime : ¬ actorPrime ∣ Nat.card normalizer := by
    intro hdiv
    exact hcoprime (hdiv.trans normalizer.card_subgroup_dvd_card)
  obtain ⟨normalizerSylow, hnormalizerSylowInvariant⟩ :=
    coprime_pgroup_exists_invariant_sylow (G := normalizer) actorPrime sylowPrime
      hpgroup hnormalizerCoprime
  have hrestrictedP : IsPGroup sylowPrime (maximal.subgroupOf normalizer) :=
    hmaximalP.of_injective (Subgroup.subgroupOfEquivOfLe
      (show maximal ≤ normalizer from Subgroup.le_normalizer)).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe
        (show maximal ≤ normalizer from Subgroup.le_normalizer)).injective
  have hrestrictedLe : maximal.subgroupOf normalizer ≤
      (normalizerSylow : Subgroup normalizer) := hrestrictedP.le_sylow_of_normal normalizerSylow
  let larger : Subgroup G := (normalizerSylow : Subgroup normalizer).map normalizer.subtype
  have hmaximalLe : maximal ≤ larger := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (show maximal ≤ normalizer from Subgroup.le_normalizer)]
    exact Subgroup.map_mono hrestrictedLe
  have hlargerInvariant : InvariantSubgroup (A := A) larger := by
    intro actor element hmem
    obtain ⟨original, horiginal, rfl⟩ := Subgroup.mem_map.mp hmem
    exact Subgroup.mem_map.mpr
      ⟨actor • original, hnormalizerSylowInvariant actor original horiginal, rfl⟩
  have hlargerMember : larger ∈ candidates :=
    ⟨hsubgroupLe.trans hmaximalLe, normalizerSylow.isPGroup'.map normalizer.subtype,
      hlargerInvariant⟩
  have hlargerEq : larger = maximal := (hmaximal.eq_of_le hlargerMember hmaximalLe).symm
  have hnormalizerLe : Subgroup.normalizer (larger : Set G) ≤ normalizer := by
    rw [hlargerEq]
  obtain ⟨ambient, hambient⟩ := sylow_inheritance_of_normalizer_le sylowPrime normalizer
    normalizerSylow hnormalizerLe
  refine ⟨ambient, ?_, ?_⟩
  · rw [← hambient]
    exact hsubgroupLe.trans hmaximalLe
  · rw [← hambient]
    exact hlargerInvariant

end CFSG.DisconnectedInvolutionGraph.Helpers
