module

public import CFSG.Mathlib.GroupTheory.Basic
public import CFSG.Open.Defs

public section

open CFSG.Open
open CFSG.Open
open scoped commutatorElement

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem nonabelian_simple_center_eq_bot
    {G : Type*} [Group G] [IsSimpleGroup G]
    (hnonab : ∃ first second : G, first * second ≠ second * first) :
    Subgroup.center G = ⊥ := by
  rcases CFSG.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with
    hbottom | htop
  · exact hbottom
  · obtain ⟨first, second, hdistinct⟩ := hnonab
    exact False.elim (hdistinct
      (Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top second) first))

theorem nonabelian_simple_isPerfect
    {G : Type*} [Group G] [IsSimpleGroup G]
    (hnonab : ∃ first second : G, first * second ≠ second * first) :
    Group.IsPerfect G := by
  apply Group.isPerfect_def.mpr
  rcases CFSG.eq_bot_or_eq_top_of_normal (commutator G) inferInstance with
    hbottom | htop
  · have hcommutative := (commutator_eq_bot_iff G).mp hbottom
    obtain ⟨first, second, hdistinct⟩ := hnonab
    exact False.elim (hdistinct (isMulCommutative_iff.mp hcommutative first second))
  · exact htop

theorem commutator_sup_central_eq
    {G : Type*} [Group G] (normalGroup centralGroup : Subgroup G)
    (hnormal : normalGroup.Normal) (hcentral : centralGroup ≤ Subgroup.center G) :
    ⁅normalGroup ⊔ centralGroup, normalGroup ⊔ centralGroup⁆ =
      ⁅normalGroup, normalGroup⁆ := by
  let : normalGroup.Normal := hnormal
  apply le_antisymm _ (Subgroup.commutator_mono le_sup_left le_sup_left)
  apply Subgroup.commutator_le.mpr
  intro first hfirst second hsecond
  obtain ⟨firstNormal, hfirstNormal, firstCentral, hfirstCentral, rfl⟩ :=
    Subgroup.mem_sup_of_normal_left.mp hfirst
  obtain ⟨secondNormal, hsecondNormal, secondCentral, hsecondCentral, rfl⟩ :=
    Subgroup.mem_sup_of_normal_left.mp hsecond
  have hfirstZero : ⁅firstCentral, secondNormal * secondCentral⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp (hcentral hfirstCentral) _).symm
  have hsecondZero : ⁅firstNormal, secondCentral⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp (hcentral hsecondCentral) _)
  rw [commutatorElement_mul_left_eq_conj_mul, hfirstZero,
    mul_one, mul_inv_cancel, one_mul,
    commutatorElement_mul_right_eq_mul_conj, hsecondZero]
  simpa only [mul_one, mul_inv_cancel_right] using
    Subgroup.commutator_mem_commutator hfirstNormal hsecondNormal

theorem surjective_perfect_image_derived_sup_kernel_eq_top
    {G Image : Type*} [Group G] [Group Image] [Group.IsPerfect Image]
    (homomorphism : G →* Image) (hsurjective : Function.Surjective homomorphism) :
    commutator G ⊔ homomorphism.ker = ⊤ := by
  have hmap : Subgroup.map homomorphism (commutator G) = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective homomorphism hsurjective,
      ← commutator_def, Group.IsPerfect.commutator_eq_top]
  have hcomap := Subgroup.comap_map_eq homomorphism (commutator G)
  rw [hmap, Subgroup.comap_top] at hcomap
  exact hcomap.symm

theorem central_extension_perfect_derived
    {G Image : Type*} [Group G] [Group Image] [Group.IsPerfect Image]
    (homomorphism : G →* Image) (hsurjective : Function.Surjective homomorphism)
    (hcentral : homomorphism.ker ≤ Subgroup.center G) :
    Group.IsPerfect (commutator G) := by
  apply Subgroup.isPerfect_iff.mpr
  have hequal := commutator_sup_central_eq (commutator G) homomorphism.ker inferInstance hcentral
  rw [surjective_perfect_image_derived_sup_kernel_eq_top homomorphism hsurjective,
    ← commutator_def] at hequal
  exact hequal.symm

theorem surjective_perfect_image_derived_surjective
    {G Image : Type*} [Group G] [Group Image] [Group.IsPerfect Image]
    (homomorphism : G →* Image) (hsurjective : Function.Surjective homomorphism) :
    Function.Surjective (homomorphism.comp (commutator G).subtype) := by
  apply MonoidHom.range_eq_top.mp
  rw [MonoidHom.range_comp, Subgroup.range_subtype, commutator_def,
    Subgroup.map_commutator, Subgroup.map_top_of_surjective homomorphism hsurjective,
    ← commutator_def, Group.IsPerfect.commutator_eq_top]

theorem surjective_centerless_image_center_eq_kernel
    {G Image : Type*} [Group G] [Group Image]
    (homomorphism : G →* Image) (hsurjective : Function.Surjective homomorphism)
    (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (hcenterless : Subgroup.center Image = ⊥) :
    Subgroup.center G = homomorphism.ker := by
  apply le_antisymm _ hcentral
  intro element helement
  have himageCenter : homomorphism element ∈ Subgroup.center Image := by
    apply Subgroup.mem_center_iff.mpr
    intro other
    obtain ⟨preimage, rfl⟩ := hsurjective other
    simpa only [map_mul] using congrArg homomorphism
      (Subgroup.mem_center_iff.mp helement preimage)
  exact Subgroup.mem_bot.mp (hcenterless ▸ himageCenter)

theorem perfect_central_extension_simple_image_quasisimple
    {G Image : Type*} [Group G] [Group Image] [Group.IsPerfect G] [IsSimpleGroup Image]
    (homomorphism : G →* Image) (hsurjective : Function.Surjective homomorphism)
    (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (hnonab : ∃ first second : Image, first * second ≠ second * first) :
    IsQuasisimple G := by
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  have hcenter := surjective_centerless_image_center_eq_kernel homomorphism hsurjective hcentral
    (nonabelian_simple_center_eq_bot hnonab)
  let quotientEquiv :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans
      (QuotientGroup.quotientKerEquivOfSurjective homomorphism hsurjective)
  exact quotientEquiv.isSimpleGroup

theorem central_extension_nonabelian_simple_derived_quasisimple
    {G Image : Type*} [Group G] [Group Image] [IsSimpleGroup Image]
    (homomorphism : G →* Image) (hsurjective : Function.Surjective homomorphism)
    (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (hnonab : ∃ first second : Image, first * second ≠ second * first) :
    IsQuasisimple (commutator G) ∧
      Function.Surjective (homomorphism.comp (commutator G).subtype) := by
  let : Group.IsPerfect Image := nonabelian_simple_isPerfect hnonab
  let : Group.IsPerfect (commutator G) := central_extension_perfect_derived
    homomorphism hsurjective hcentral
  have hderivedSurjective := surjective_perfect_image_derived_surjective homomorphism hsurjective
  have hderivedCentral : (homomorphism.comp (commutator G).subtype).ker ≤
      Subgroup.center (commutator G) := by
    intro element helement
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hcentral helement) other.val
  exact ⟨perfect_central_extension_simple_image_quasisimple _ hderivedSurjective
    hderivedCentral hnonab, hderivedSurjective⟩

end CFSG.RankThreeCoreUniqueness.Helpers
