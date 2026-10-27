module

public import Mathlib
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.SolvableKernelContainment
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionDiagonal
public import CFSG.LocalAnalysis.ComponentClassification.PerfectCentralQuotient
public import CFSG.LocalAnalysis.ComponentClassification.FixedNormalCentralizer

public section

namespace CFSG.ComponentClassification.OuterAutomorphisms

@[expose] noncomputable def inner (G : Type*) [Group G] : Subgroup (MulAut G) :=
  (MulAut.conj : G →* MulAut G).range

theorem inner_normal (G : Type*) [Group G] : (inner G).Normal := by
  constructor
  intro automorphism hautomorphism conjugator
  obtain ⟨element, rfl⟩ := hautomorphism
  refine ⟨conjugator element, ?_⟩
  apply MulEquiv.ext
  intro member
  change conjugator element * member * (conjugator element)⁻¹ =
    conjugator (element * conjugator.symm member * element⁻¹)
  rw [map_mul, map_mul, map_inv, conjugator.apply_symm_apply]

noncomputable instance innerNormal (G : Type*) [Group G] : (inner G).Normal :=
  inner_normal G

noncomputable abbrev Outer (G : Type*) [Group G] := MulAut G ⧸ inner G

theorem congr_conj {G H : Type*} [Group G] [Group H] (equivalence : G ≃* H) (element : G) :
    MulAut.congr equivalence (MulAut.conj element) = MulAut.conj (equivalence element) := by
  apply MulEquiv.ext
  intro member
  change equivalence (element * equivalence.symm member * element⁻¹) =
    equivalence element * member * (equivalence element)⁻¹
  rw [map_mul, map_mul, map_inv, equivalence.apply_symm_apply]

theorem inner_map_congr {G H : Type*} [Group G] [Group H] (equivalence : G ≃* H) :
    (inner G).map (MulAut.congr equivalence).toMonoidHom = inner H := by
  ext automorphism
  constructor
  · rintro ⟨lift, ⟨element, rfl⟩, rfl⟩
    exact ⟨equivalence element, (congr_conj equivalence element).symm⟩
  · rintro ⟨element, rfl⟩
    refine ⟨MulAut.conj (equivalence.symm element), ⟨equivalence.symm element, rfl⟩, ?_⟩
    exact (congr_conj equivalence (equivalence.symm element)).trans
      (congrArg MulAut.conj (equivalence.apply_symm_apply element))

@[expose] noncomputable def equivalence {G H : Type*} [Group G] [Group H] (groupEquivalence : G ≃* H) :
    Outer G ≃* Outer H :=
  QuotientGroup.congr (inner G) (inner H) (MulAut.congr groupEquivalence)
    (inner_map_congr groupEquivalence)

theorem solvable_of_equiv {G H : Type*} [Group G] [Group H] (groupEquivalence : G ≃* H)
    [Group.IsSolvable (Outer G)] : Group.IsSolvable (Outer H) :=
  Group.isSolvable_of_surjective (equivalence groupEquivalence).surjective

theorem center_map_equiv {G H : Type*} [Group G] [Group H] (groupEquivalence : G ≃* H) :
    (Subgroup.center G).map groupEquivalence.toMonoidHom = Subgroup.center H := by
  ext member
  constructor
  · rintro ⟨lift, hlift, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro other
    obtain ⟨original, rfl⟩ := groupEquivalence.surjective other
    change groupEquivalence original * groupEquivalence lift = groupEquivalence lift * groupEquivalence original
    simpa only [map_mul] using congrArg groupEquivalence (Subgroup.mem_center_iff.mp hlift original)
  · intro hmember
    refine ⟨groupEquivalence.symm member, ?_, groupEquivalence.apply_symm_apply member⟩
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply groupEquivalence.injective
    simpa only [map_mul, groupEquivalence.apply_symm_apply] using
      Subgroup.mem_center_iff.mp hmember (groupEquivalence other)

theorem solvable_centerQuotient_of_equiv {G H : Type*} [Group G] [Group H]
    (groupEquivalence : G ≃* H) [Group.IsSolvable (Outer (G ⧸ Subgroup.center G))] :
    Group.IsSolvable (Outer (H ⧸ Subgroup.center H)) :=
  solvable_of_equiv (QuotientGroup.congr (Subgroup.center G) (Subgroup.center H)
    groupEquivalence (center_map_equiv groupEquivalence))

theorem centerQuotient_conj {G : Type*} [Group G] (element : G) :
    PerfectAutomorphisms.centerQuotientHom G (MulAut.conj element) =
      MulAut.conj ((QuotientGroup.mk' (Subgroup.center G)) element) := by
  apply MulEquiv.ext
  intro member
  obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) member
  rw [MulAut.conj_apply]
  change PerfectAutomorphisms.onCenterQuotient (MulAut.conj element)
    ((QuotientGroup.mk' (Subgroup.center G)) lift) = _
  rw [PerfectAutomorphisms.onCenterQuotient_apply_mk, MulAut.conj_apply,
    map_mul, map_mul, map_inv]

theorem centerQuotient_inner_le {G : Type*} [Group G] :
    inner G ≤ (inner (G ⧸ Subgroup.center G)).comap
      (PerfectAutomorphisms.centerQuotientHom G) := by
  intro automorphism hautomorphism
  obtain ⟨element, rfl⟩ := hautomorphism
  exact ⟨(QuotientGroup.mk' (Subgroup.center G)) element, (centerQuotient_conj element).symm⟩

@[expose] noncomputable def centerQuotientOuterHom (G : Type*) [Group G] :
    Outer G →* Outer (G ⧸ Subgroup.center G) :=
  QuotientGroup.map (inner G) (inner (G ⧸ Subgroup.center G))
    (PerfectAutomorphisms.centerQuotientHom G) centerQuotient_inner_le

theorem centerQuotient_outer_injective (G : Type*) [Group G] [Group.IsPerfect G] :
    Function.Injective (centerQuotientOuterHom G) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro member hmember
  obtain ⟨automorphism, rfl⟩ := QuotientGroup.mk'_surjective (inner G) member
  have hinner : PerfectAutomorphisms.centerQuotientHom G automorphism ∈
      inner (G ⧸ Subgroup.center G) := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact hmember
  obtain ⟨quotientElement, hquotientElement⟩ := hinner
  obtain ⟨element, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) quotientElement
  have heq : MulAut.conj element = automorphism :=
    PerfectAutomorphisms.centerQuotientHom_injective G
      ((centerQuotient_conj element).trans hquotientElement)
  apply Subgroup.mem_bot.mpr
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ⟨element, heq⟩

theorem solvable_of_centerQuotient (G : Type*) [Group G] [Group.IsPerfect G]
    [Group.IsSolvable (Outer (G ⧸ Subgroup.center G))] : Group.IsSolvable (Outer G) :=
  Group.isSolvable_of_isSolvable_injective (centerQuotient_outer_injective G)

theorem perfect_action_inner {A G : Type*} [Group A] [Group.IsPerfect A] [Group G]
    [Group.IsSolvable (Outer G)] (action : A →* MulAut G) (actor : A) :
    ∃ element : G, action actor = MulAut.conj element := by
  have htrivial := SolvableKernelContainment.hom_eq_one
    ((QuotientGroup.mk' (inner G)).comp action)
  have hone := congrArg (fun homomorphism : A →* Outer G => homomorphism actor) htrivial
  have hinner : action actor ∈ inner G := (QuotientGroup.eq_one_iff _).mp hone
  obtain ⟨element, heq⟩ := hinner
  exact ⟨element, heq.symm⟩

end CFSG.ComponentClassification.OuterAutomorphisms
