module

public import CFSG.Assembly.Defs

public section

open scoped commutatorElement

namespace CFSG.ComponentClassification.CommutingFamilyCentralQuotient

@[expose] noncomputable def ambient {G Index : Type*} [Group G] [Fintype Index]
    (family : Index → Subgroup G)
    (hcommutes : Pairwise (fun first second => ∀ left right : G,
      left ∈ family first → right ∈ family second → Commute left right)) :
    ((index : Index) → family index) →* G := Subgroup.noncommPiCoprod hcommutes

theorem range {G Index : Type*} [Group G] [Fintype Index]
    (family : Index → Subgroup G)
    (hcommutes : Pairwise (fun first second => ∀ left right : G,
      left ∈ family first → right ∈ family second → Commute left right)) :
    (ambient family hcommutes).range = ⨆ index, family index := Subgroup.noncommPiCoprod_range

@[expose] noncomputable def multiplication {G Index : Type*} [Group G] [Fintype Index]
    (family : Index → Subgroup G)
    (hcommutes : Pairwise (fun first second => ∀ left right : G,
      left ∈ family first → right ∈ family second → Commute left right)) :
    ((index : Index) → family index) →* ↥(⨆ index, family index) :=
  (ambient family hcommutes).codRestrict (⨆ index, family index) (fun tuple => range family hcommutes ▸ ⟨tuple, rfl⟩)

theorem surjective {G Index : Type*} [Group G] [Fintype Index]
    (family : Index → Subgroup G)
    (hcommutes : Pairwise (fun first second => ∀ left right : G,
      left ∈ family first → right ∈ family second → Commute left right)) :
    Function.Surjective (multiplication family hcommutes) := by
  intro member
  have hmember : member.val ∈ (ambient family hcommutes).range := (range family hcommutes).symm ▸ member.property
  obtain ⟨tuple, heq⟩ := hmember
  exact ⟨tuple, Subtype.ext heq⟩

theorem tuple_center {G Index : Type*} [Group G] [Fintype Index]
    (family : Index → Subgroup G) (tuple : (index : Index) → family index) :
    tuple ∈ Subgroup.center ((index : Index) → family index) ↔
      ∀ index, tuple index ∈ Subgroup.center (family index) := by
  classical
  constructor
  · intro hcentral index
    apply Subgroup.mem_center_iff.mpr
    intro member
    have heq := congrArg (fun tuple : (index : Index) → family index => tuple index)
      (Subgroup.mem_center_iff.mp hcentral (Pi.mulSingle index member))
    simpa only [Pi.mul_apply, Pi.mulSingle_eq_same] using heq
  · intro hcentral
    apply Subgroup.mem_center_iff.mpr
    intro other
    funext index
    exact Subgroup.mem_center_iff.mp (hcentral index) (other index)

theorem central_preimage {G Index : Type*} [Group G] [Fintype Index]
    (family : Index → Subgroup G)
    (hcommutes : Pairwise (fun first second => ∀ left right : G,
      left ∈ family first → right ∈ family second → Commute left right))
    (tuple : (index : Index) → family index) :
    multiplication family hcommutes tuple ∈ Subgroup.center ↥(⨆ index, family index) ↔
      tuple ∈ Subgroup.center ((index : Index) → family index) := by
  classical
  constructor
  · intro hcentral
    apply (tuple_center family tuple).mpr
    intro index
    apply Subgroup.mem_center_iff.mpr
    intro member
    have hcoordinateCommutator : ⁅tuple, Pi.mulSingle (M := fun index : Index => ↥(family index)) index member⁆ =
        Pi.mulSingle (M := fun index : Index => ↥(family index)) index ⁅tuple index, member⁆ := by
      funext other
      have hcommutatorApply : ⁅tuple, Pi.mulSingle (M := fun index : Index => ↥(family index)) index member⁆ other =
          ⁅tuple other, Pi.mulSingle (M := fun index : Index => ↥(family index)) index member other⁆ := by
        simp only [commutatorElement_def, Pi.mul_apply, Pi.inv_apply]
      rw [hcommutatorApply]
      by_cases heq : other = index
      · subst other
        simp only [Pi.mulSingle_eq_same]
      · simp only [Pi.mulSingle_eq_of_ne heq, commutatorElement_one_right]
    have hmap := map_commutatorElement (multiplication family hcommutes) tuple
      (Pi.mulSingle (M := fun index : Index => ↥(family index)) index member)
    have hcommutatorOne : ⁅multiplication family hcommutes tuple,
        multiplication family hcommutes (Pi.mulSingle (M := fun index : Index => ↥(family index)) index member)⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hcentral _).symm
    rw [hcommutatorOne, hcoordinateCommutator] at hmap
    have hvalue := Subgroup.noncommPiCoprod_mulSingle (H := family) (hcomm := hcommutes) index ⁅tuple index, member⁆
    have hone : (⁅tuple index, member⁆ : family index).val = 1 := hvalue.symm.trans (congrArg Subtype.val hmap)
    exact (commutatorElement_eq_one_iff_mul_comm.mp (Subtype.ext hone)).symm
  · intro hcentral
    apply Subgroup.mem_center_iff.mpr
    intro member
    obtain ⟨other, rfl⟩ := surjective family hcommutes member
    rw [← map_mul, ← map_mul]
    exact congrArg (multiplication family hcommutes) (Subgroup.mem_center_iff.mp hcentral other)

@[expose] noncomputable def coordinateMap {G Index : Type*} [Group G]
    (family : Index → Subgroup G) :
    ((index : Index) → family index) →* ((index : Index) → (family index) ⧸ Subgroup.center (family index)) :=
  MonoidHom.piMap (fun index => QuotientGroup.mk' (Subgroup.center (family index)))

theorem coordinate_surjective {G Index : Type*} [Group G]
    (family : Index → Subgroup G) : Function.Surjective (coordinateMap family) := by
  intro tuple
  choose lift hlift using fun index => QuotientGroup.mk'_surjective (Subgroup.center (family index)) (tuple index)
  exact ⟨lift, funext hlift⟩

theorem coordinate_kernel {G Index : Type*} [Group G] [Fintype Index]
    (family : Index → Subgroup G) :
    (coordinateMap family).ker = Subgroup.center ((index : Index) → family index) := by
  ext tuple
  rw [MonoidHom.mem_ker, tuple_center]
  constructor
  · intro heq index
    have hcoordinate := congrArg (fun tuple : (index : Index) → (family index) ⧸ Subgroup.center (family index) => tuple index) heq
    exact (QuotientGroup.eq_one_iff (tuple index)).mp hcoordinate
  · intro hcentral
    funext index
    exact (QuotientGroup.eq_one_iff (tuple index)).mpr (hcentral index)

@[expose] noncomputable def quotientMap {G Index : Type*} [Group G] [Fintype Index]
    (family : Index → Subgroup G)
    (hcommutes : Pairwise (fun first second => ∀ left right : G,
      left ∈ family first → right ∈ family second → Commute left right)) :
    ((index : Index) → family index) →* ↥(⨆ index, family index) ⧸ Subgroup.center ↥(⨆ index, family index) :=
  (QuotientGroup.mk' (Subgroup.center ↥(⨆ index, family index))).comp (multiplication family hcommutes)

theorem quotient_surjective {G Index : Type*} [Group G] [Fintype Index]
    (family : Index → Subgroup G)
    (hcommutes : Pairwise (fun first second => ∀ left right : G,
      left ∈ family first → right ∈ family second → Commute left right)) :
    Function.Surjective (quotientMap family hcommutes) :=
  (QuotientGroup.mk'_surjective _).comp (surjective family hcommutes)

theorem quotient_kernel {G Index : Type*} [Group G] [Fintype Index]
    (family : Index → Subgroup G)
    (hcommutes : Pairwise (fun first second => ∀ left right : G,
      left ∈ family first → right ∈ family second → Commute left right)) :
    (quotientMap family hcommutes).ker = Subgroup.center ((index : Index) → family index) := by
  ext tuple
  rw [MonoidHom.mem_ker]
  exact (QuotientGroup.eq_one_iff (multiplication family hcommutes tuple)).trans (central_preimage family hcommutes tuple)

@[expose] noncomputable def equivalence {G Index : Type*} [Group G] [Fintype Index]
    (family : Index → Subgroup G)
    (hcommutes : Pairwise (fun first second => ∀ left right : G,
      left ∈ family first → right ∈ family second → Commute left right)) :
    ↥(⨆ index, family index) ⧸ Subgroup.center ↥(⨆ index, family index) ≃*
      ((index : Index) → (family index) ⧸ Subgroup.center (family index)) :=
  (QuotientGroup.liftEquiv (Subgroup.center ((index : Index) → family index))
    (quotient_surjective family hcommutes) (quotient_kernel family hcommutes).symm).symm.trans
      (QuotientGroup.liftEquiv (Subgroup.center ((index : Index) → family index))
        (coordinate_surjective family) (coordinate_kernel family).symm)

theorem equivalence_apply {G Index : Type*} [Group G] [Fintype Index]
    (family : Index → Subgroup G)
    (hcommutes : Pairwise (fun first second => ∀ left right : G,
      left ∈ family first → right ∈ family second → Commute left right))
    (tuple : (index : Index) → family index) :
    equivalence family hcommutes (quotientMap family hcommutes tuple) = coordinateMap family tuple := by
  let firstEquivalence := QuotientGroup.liftEquiv (Subgroup.center ((index : Index) → family index))
    (quotient_surjective family hcommutes) (quotient_kernel family hcommutes).symm
  let secondEquivalence := QuotientGroup.liftEquiv (Subgroup.center ((index : Index) → family index))
    (coordinate_surjective family) (coordinate_kernel family).symm
  change secondEquivalence (firstEquivalence.symm (quotientMap family hcommutes tuple)) = _
  have hfirst : firstEquivalence ((QuotientGroup.mk' (Subgroup.center ((index : Index) → family index))) tuple) =
      quotientMap family hcommutes tuple := QuotientGroup.liftEquiv_mk _ _ _ _
  rw [← hfirst, firstEquivalence.symm_apply_apply]
  exact QuotientGroup.liftEquiv_mk _ _ _ _

@[expose] noncomputable def coordinates {G Index : Type*} [Group G] [Fintype Index]
    (family : Index → Subgroup G)
    (hcommutes : Pairwise (fun first second => ∀ left right : G,
      left ∈ family first → right ∈ family second → Commute left right)) :
    ↥(⨆ index, family index) →* ((index : Index) → (family index) ⧸ Subgroup.center (family index)) :=
  (equivalence family hcommutes).toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥(⨆ index, family index)))

theorem coordinates_multiplication {G Index : Type*} [Group G] [Fintype Index]
    (family : Index → Subgroup G)
    (hcommutes : Pairwise (fun first second => ∀ left right : G,
      left ∈ family first → right ∈ family second → Commute left right))
    (tuple : (index : Index) → family index) :
    coordinates family hcommutes (multiplication family hcommutes tuple) = coordinateMap family tuple :=
  equivalence_apply family hcommutes tuple

theorem coordinates_surjective {G Index : Type*} [Group G] [Fintype Index]
    (family : Index → Subgroup G)
    (hcommutes : Pairwise (fun first second => ∀ left right : G,
      left ∈ family first → right ∈ family second → Commute left right)) :
    Function.Surjective (coordinates family hcommutes) :=
  (equivalence family hcommutes).surjective.comp (QuotientGroup.mk'_surjective _)

theorem coordinates_kernel {G Index : Type*} [Group G] [Fintype Index]
    (family : Index → Subgroup G)
    (hcommutes : Pairwise (fun first second => ∀ left right : G,
      left ∈ family first → right ∈ family second → Commute left right)) :
    (coordinates family hcommutes).ker = Subgroup.center ↥(⨆ index, family index) := by
  ext member
  rw [MonoidHom.mem_ker]
  change equivalence family hcommutes ((QuotientGroup.mk' (Subgroup.center ↥(⨆ index, family index))) member) = 1 ↔ _
  rw [← map_one (equivalence family hcommutes), (equivalence family hcommutes).injective.eq_iff]
  exact QuotientGroup.eq_one_iff member

theorem multiplication_mem {G Index : Type*} [Group G] [Fintype Index]
    (family : Index → Subgroup G)
    (hcommutes : Pairwise (fun first second => ∀ left right : G,
      left ∈ family first → right ∈ family second → Commute left right))
    (tuple : (index : Index) → family index) (subgroup : Subgroup G)
    (hcontained : ∀ index, (tuple index).val ∈ subgroup) :
    (multiplication family hcommutes tuple).val ∈ subgroup := by
  change ambient family hcommutes tuple ∈ subgroup
  rw [ambient, Subgroup.noncommPiCoprod_apply]
  exact subgroup.noncommProd_mem _ (fun index _ => hcontained index)

theorem multiplication_single {G Index : Type*} [Group G] [Fintype Index]
    (family : Index → Subgroup G)
    (hcommutes : Pairwise (fun first second => ∀ left right : G,
      left ∈ family first → right ∈ family second → Commute left right))
    [DecidableEq Index] (index : Index) (member : family index) :
    (multiplication family hcommutes (Pi.mulSingle (M := fun index : Index => ↥(family index)) index member)).val = member.val :=
  Subgroup.noncommPiCoprod_mulSingle index member

theorem commutator_single {G Index : Type*} [Group G] [Fintype Index]
    (family : Index → Subgroup G) [DecidableEq Index]
    (tuple : (index : Index) → family index) (index : Index) (member : family index) :
    ⁅tuple, Pi.mulSingle (M := fun index : Index => ↥(family index)) index member⁆ =
      Pi.mulSingle (M := fun index : Index => ↥(family index)) index ⁅tuple index, member⁆ := by
  funext other
  have hcommutatorApply : ⁅tuple, Pi.mulSingle (M := fun index : Index => ↥(family index)) index member⁆ other =
      ⁅tuple other, Pi.mulSingle (M := fun index : Index => ↥(family index)) index member other⁆ := by
    simp only [commutatorElement_def, Pi.mul_apply, Pi.inv_apply]
  rw [hcommutatorApply]
  by_cases heq : other = index
  · subst other
    simp only [Pi.mulSingle_eq_same]
  · simp only [Pi.mulSingle_eq_of_ne heq, commutatorElement_one_right]

theorem coordinates_eq_one_iff {G Index : Type*} [Group G] [Fintype Index]
    (family : Index → Subgroup G)
    (hcommutes : Pairwise (fun first second => ∀ left right : G,
      left ∈ family first → right ∈ family second → Commute left right))
    (member : ↥(⨆ index, family index)) (index : Index) :
    coordinates family hcommutes member index = 1 ↔ member.val ∈ Subgroup.centralizer (family index : Set G) := by
  classical
  obtain ⟨tuple, htuple⟩ := surjective family hcommutes member
  rw [← htuple, coordinates_multiplication]
  change (QuotientGroup.mk' (Subgroup.center (family index))) (tuple index) = 1 ↔ _
  have hquotient : (QuotientGroup.mk' (Subgroup.center (family index))) (tuple index) = 1 ↔
      tuple index ∈ Subgroup.center (family index) := QuotientGroup.eq_one_iff (tuple index)
  rw [hquotient]
  have hmap : ∀ other : family index,
      ⁅(multiplication family hcommutes tuple).val, other.val⁆ = (⁅tuple index, other⁆ : family index).val := by
    intro other
    have heq := map_commutatorElement (ambient family hcommutes) tuple
      (Pi.mulSingle (M := fun index : Index => ↥(family index)) index other)
    rw [commutator_single, ambient, Subgroup.noncommPiCoprod_mulSingle, Subgroup.noncommPiCoprod_mulSingle] at heq
    exact heq.symm
  constructor
  · intro hcentral
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    have hone : ⁅tuple index, (⟨other, hother⟩ : family index)⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hcentral _).symm
    have hcommutator := hmap ⟨other, hother⟩
    rw [hone] at hcommutator
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcommutator).symm
  · intro hcentral
    apply Subgroup.mem_center_iff.mpr
    intro other
    have hone : ⁅(multiplication family hcommutes tuple).val, other.val⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hcentral other.val other.property).symm
    rw [hmap] at hone
    exact (commutatorElement_eq_one_iff_mul_comm.mp (Subtype.ext hone)).symm

end CFSG.ComponentClassification.CommutingFamilyCentralQuotient
