module

public import CFSG.LocalAnalysis.ComponentClassification.CommutingFamilyCentralQuotient

public section

namespace CFSG.ComponentClassification.CommutingFamilySupport

@[expose] noncomputable def subproduct {G Index : Type*} [Group G]
    (family : Index → Subgroup G) (subset : Set Index) : Subgroup G := ⨆ index ∈ subset, family index

theorem partial_le {G Index : Type*} [Group G]
    (family : Index → Subgroup G) (subset : Set Index) : subproduct family subset ≤ ⨆ index, family index :=
  iSup_le (fun index => iSup_le (fun _ => le_iSup family index))

theorem support_iff {G Index : Type*} [Group G] [Fintype Index]
    (family : Index → Subgroup G)
    (hcommutes : Pairwise (fun first second => ∀ left right : G,
      left ∈ family first → right ∈ family second → Commute left right))
    (subset : Set Index) (member : ↥(⨆ index, family index)) :
    (∀ index ∉ subset, CommutingFamilyCentralQuotient.coordinates family hcommutes member index = 1) ↔
      member.val ∈ subproduct family subset ⊔ (Subgroup.center ↥(⨆ index, family index)).map (⨆ index, family index).subtype := by
  classical
  let generated : Subgroup G := ⨆ index, family index
  let coordinates := CommutingFamilyCentralQuotient.coordinates family hcommutes
  constructor
  · intro hsupport
    obtain ⟨tuple, htuple⟩ := CommutingFamilyCentralQuotient.surjective family hcommutes member
    let selected : (index : Index) → family index := fun index => if index ∈ subset then tuple index else 1
    let residual : (index : Index) → family index := fun index => if index ∈ subset then 1 else tuple index
    have hproduct : selected * residual = tuple := by
      funext index
      by_cases hindex : index ∈ subset <;> simp only [selected, residual, Pi.mul_apply, hindex, ite_true, ite_false, mul_one, one_mul]
    have hselected : (CommutingFamilyCentralQuotient.multiplication family hcommutes selected).val ∈ subproduct family subset := by
      apply CommutingFamilyCentralQuotient.multiplication_mem
      intro index
      by_cases hindex : index ∈ subset
      · change (if index ∈ subset then tuple index else 1).val ∈ subproduct family subset
        rw [ite_eq_left hindex]
        have hfactor : family index ≤ subproduct family subset := le_iSup_of_le index (le_iSup_of_le hindex le_rfl)
        exact hfactor (tuple index).property
      · change (if index ∈ subset then tuple index else 1).val ∈ subproduct family subset
        rw [ite_eq_right hindex]
        exact (subproduct family subset).one_mem
    have hresidual : residual ∈ Subgroup.center ((index : Index) → family index) := by
      apply (CommutingFamilyCentralQuotient.tuple_center family residual).mpr
      intro index
      by_cases hindex : index ∈ subset
      · change (if index ∈ subset then 1 else tuple index) ∈ Subgroup.center (family index)
        rw [ite_eq_left hindex]
        exact (Subgroup.center (family index)).one_mem
      · have hcoordinate := hsupport index hindex
        rw [← htuple, CommutingFamilyCentralQuotient.coordinates_multiplication] at hcoordinate
        have hcentral := (QuotientGroup.eq_one_iff (tuple index)).mp hcoordinate
        change (if index ∈ subset then 1 else tuple index) ∈ Subgroup.center (family index)
        rw [ite_eq_right hindex]
        exact hcentral
    have hresidualImage := (CommutingFamilyCentralQuotient.central_preimage family hcommutes residual).mpr hresidual
    have hmemberEq := congrArg (CommutingFamilyCentralQuotient.multiplication family hcommutes) hproduct
    rw [map_mul, htuple] at hmemberEq
    rw [← congrArg Subtype.val hmemberEq]
    exact (subproduct family subset ⊔ (Subgroup.center generated).map generated.subtype).mul_mem
      ((le_sup_left : subproduct family subset ≤ subproduct family subset ⊔ (Subgroup.center generated).map generated.subtype) hselected)
      ((le_sup_right : (Subgroup.center generated).map generated.subtype ≤ subproduct family subset ⊔
        (Subgroup.center generated).map generated.subtype) (Subgroup.mem_map.mpr
        ⟨CommutingFamilyCentralQuotient.multiplication family hcommutes residual, hresidualImage, rfl⟩))
  · intro hmember
    let vanishing : Subgroup generated :=
      { carrier := fun element => ∀ index ∉ subset, coordinates element index = 1
        one_mem' := by intro index _; rw [map_one]; rfl
        mul_mem' := by
          intro first second hfirst hsecond index hindex
          change coordinates (first * second) index = 1
          rw [map_mul]
          change coordinates first index * coordinates second index = 1
          rw [hfirst index hindex, hsecond index hindex, one_mul]
        inv_mem' := by
          intro element helement index hindex
          change coordinates element⁻¹ index = 1
          rw [map_inv]
          change (coordinates element index)⁻¹ = 1
          rw [helement index hindex, inv_one] }
    have hpartial : subproduct family subset ≤ vanishing.map generated.subtype := by
      apply iSup_le
      intro index
      apply iSup_le
      intro hindex element helement
      let tuple := Pi.mulSingle (M := fun index : Index => ↥(family index)) index (⟨element, helement⟩ : family index)
      let lift := CommutingFamilyCentralQuotient.multiplication family hcommutes tuple
      refine Subgroup.mem_map.mpr ⟨lift, ?_, CommutingFamilyCentralQuotient.multiplication_single family hcommutes index _⟩
      intro other hother
      change CommutingFamilyCentralQuotient.coordinates family hcommutes lift other = 1
      rw [CommutingFamilyCentralQuotient.coordinates_multiplication]
      change (QuotientGroup.mk' (Subgroup.center (family other))) (tuple other) = 1
      have hne : other ≠ index := by
        intro heq
        subst other
        exact hother hindex
      dsimp only [tuple]
      rw [Pi.mulSingle_eq_of_ne hne, map_one]
    have hcenter : (Subgroup.center generated).map generated.subtype ≤ vanishing.map generated.subtype := by
      apply Subgroup.map_mono
      intro element helement index _
      have hone : coordinates element = 1 := by
        apply MonoidHom.mem_ker.mp
        rw [CommutingFamilyCentralQuotient.coordinates_kernel]
        exact helement
      exact congrArg (fun tuple : (index : Index) → (family index) ⧸ Subgroup.center (family index) => tuple index) hone
    obtain ⟨lift, hlift, heq⟩ := Subgroup.mem_map.mp ((sup_le hpartial hcenter) hmember)
    have hliftEq : lift = member := Subtype.ext heq
    rw [hliftEq] at hlift
    exact hlift

@[expose] def support {G Index : Type*} [Group G]
    (family : Index → Subgroup G) (member : G) : Set Index :=
  {index | member ∉ Subgroup.centralizer (family index : Set G)}

theorem support_coordinates {G Index : Type*} [Group G] [Fintype Index]
    (family : Index → Subgroup G)
    (hcommutes : Pairwise (fun first second => ∀ left right : G,
      left ∈ family first → right ∈ family second → Commute left right))
    (member : ↥(⨆ index, family index)) (index : Index) :
    index ∈ support family member.val ↔ CommutingFamilyCentralQuotient.coordinates family hcommutes member index ≠ 1 :=
  not_congr (CommutingFamilyCentralQuotient.coordinates_eq_one_iff family hcommutes member index).symm

theorem support_subproduct {G Index : Type*} [Group G] [Fintype Index]
    (family : Index → Subgroup G)
    (hcommutes : Pairwise (fun first second => ∀ left right : G,
      left ∈ family first → right ∈ family second → Commute left right))
    (subset : Set Index) (member : ↥(⨆ index, family index)) :
    support family member.val ⊆ subset ↔
      member.val ∈ subproduct family subset ⊔ (Subgroup.center ↥(⨆ index, family index)).map (⨆ index, family index).subtype := by
  rw [← support_iff family hcommutes subset member]
  constructor
  · intro hsupport index hindex
    apply (CommutingFamilyCentralQuotient.coordinates_eq_one_iff family hcommutes member index).mpr
    by_contra hnot
    exact hindex (hsupport hnot)
  · intro hcoordinates index hindex
    by_contra hnot
    exact (support_coordinates family hcommutes member index).mp hindex (hcoordinates index hnot)

theorem centralizer_transport {G : Type*} [Group G]
    (automorphism : G ≃* G) (factor : Subgroup G) (member : G) :
    automorphism member ∈ Subgroup.centralizer (factor.map automorphism.toMonoidHom : Set G) ↔
      member ∈ Subgroup.centralizer (factor : Set G) := by
  constructor
  · intro hcentral
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    apply automorphism.injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hcentral (automorphism other) (Subgroup.mem_map.mpr ⟨other, hother, rfl⟩)
  · intro hcentral
    apply Subgroup.mem_centralizer_iff.mpr
    rintro other ⟨lift, hlift, rfl⟩
    change automorphism lift * automorphism member = automorphism member * automorphism lift
    rw [← map_mul, ← map_mul]
    exact congrArg automorphism (Subgroup.mem_centralizer_iff.mp hcentral lift hlift)

theorem support_transport {G Index : Type*} [Group G]
    (family : Index → Subgroup G) (automorphism : G ≃* G) (permutation : Equiv.Perm Index)
    (hfamily : ∀ index, (family index).map automorphism.toMonoidHom = family (permutation index)) (member : G) :
    support family (automorphism member) = permutation '' support family member := by
  ext index
  constructor
  · intro hindex
    refine ⟨permutation.symm index, ?_, permutation.apply_symm_apply index⟩
    change member ∉ Subgroup.centralizer (family (permutation.symm index) : Set G)
    have htransport := centralizer_transport automorphism (family (permutation.symm index)) member
    rw [hfamily, permutation.apply_symm_apply] at htransport
    exact hindex ∘ htransport.mpr
  · rintro ⟨original, horiginal, rfl⟩
    change automorphism member ∉ Subgroup.centralizer (family (permutation original) : Set G)
    rw [← hfamily original]
    exact horiginal ∘ (centralizer_transport automorphism (family original) member).mp

end CFSG.ComponentClassification.CommutingFamilySupport
