module

public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.ComponentClassification.CenterlessCommutingFamily

theorem disjoint_of_centralizes {G : Type*} [Group G] (factor other : Subgroup G)
    (hcenter : Subgroup.center factor = ⊥) (hcentralizes : other ≤ Subgroup.centralizer (factor : Set G)) :
    Disjoint factor other := by
  apply disjoint_iff.mpr
  apply le_antisymm _ bot_le
  intro member hmember
  have hcentral : (⟨member, hmember.1⟩ : factor) ∈ Subgroup.center factor := by
    apply Subgroup.mem_center_iff.mpr
    intro another
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp
      (hcentralizes hmember.2) another.val another.property)
  rw [hcenter, Subgroup.mem_bot] at hcentral
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hcentral)

theorem family_independent {G : Type*} [Group G] {Index : Type*}
    (factors : Index → Subgroup G)
    (hcenter : ∀ index, Subgroup.center (factors index) = ⊥)
    (hcommutes : Pairwise (fun first second => ⁅factors first, factors second⁆ = ⊥)) :
    iSupIndep factors := by
  apply iSupIndep_def.mpr
  intro index
  apply disjoint_of_centralizes _ _ (hcenter index)
  apply iSup_le
  intro other
  apply iSup_le
  intro hne
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcommutes hne)

theorem sup_disjoint_of_centralizes {G : Type*} [Group G] (factor other remainder : Subgroup G)
    [factor.Normal] (hcenter : Subgroup.center factor = ⊥)
    (hotherCentralizes : other ≤ Subgroup.centralizer (factor : Set G))
    (hremainderCentralizes : remainder ≤ Subgroup.centralizer (factor : Set G))
    (hdisjoint : Disjoint other remainder) : Disjoint (factor ⊔ other) remainder := by
  apply disjoint_iff.mpr
  apply le_antisymm _ bot_le
  intro member hmember
  obtain ⟨first, hfirst, second, hsecond, heq⟩ :=
    Subgroup.mem_sup_of_normal_left.mp hmember.1
  have hfirstCentralizes : first ∈ Subgroup.centralizer (factor : Set G) := by
    have hproduct : first * second ∈ Subgroup.centralizer (factor : Set G) :=
      heq ▸ hremainderCentralizes hmember.2
    have hmem := (Subgroup.centralizer (factor : Set G)).mul_mem hproduct
      ((Subgroup.centralizer (factor : Set G)).inv_mem (hotherCentralizes hsecond))
    simpa only [mul_inv_cancel_right] using hmem
  have hfirstOne : first = 1 := by
    have hdisjointCenter := disjoint_of_centralizes factor
      (Subgroup.centralizer (factor : Set G)) hcenter le_rfl
    exact Subgroup.mem_bot.mp (hdisjointCenter.eq_bot ▸
      (show first ∈ factor ⊓ Subgroup.centralizer (factor : Set G) from ⟨hfirst, hfirstCentralizes⟩))
  have hsecondEq : second = member := by simpa only [hfirstOne, one_mul] using heq
  have hsecondOne : second = 1 := Subgroup.mem_bot.mp (hdisjoint.eq_bot ▸
    (show second ∈ other ⊓ remainder from ⟨hsecond, hsecondEq ▸ hmember.2⟩))
  exact Subgroup.mem_bot.mpr (heq.symm.trans (by rw [hfirstOne, hsecondOne, one_mul]))

theorem finset_disjoint_sup {G : Type*} [Group G] {Index : Type*}
    (factors : Index → Subgroup G) (hnormal : ∀ index, (factors index).Normal)
    (hcenter : ∀ index, Subgroup.center (factors index) = ⊥)
    (hcommutes : Pairwise (fun first second => ⁅factors first, factors second⁆ = ⊥))
    (first second : Finset Index) (hdisjoint : Disjoint first second) :
    Disjoint (first.sup factors) (second.sup factors) := by
  classical
  induction first using Finset.induction_on with
  | empty => simp only [Finset.sup_empty, disjoint_bot_left]
  | @insert index remaining hnotMem hinduction =>
      rw [Finset.sup_insert]
      let : (factors index).Normal := hnormal index
      apply sup_disjoint_of_centralizes _ _ _ (hcenter index)
      · apply Finset.sup_le
        intro other hother
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcommutes (by
          intro heq
          exact hnotMem (heq ▸ hother)))
      · apply Finset.sup_le
        intro other hother
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcommutes (by
          intro heq
          exact Finset.disjoint_left.mp hdisjoint (Finset.mem_insert_self index remaining)
            (heq ▸ hother)))
      · exact hinduction (hdisjoint.mono_left (Finset.subset_insert _ _))

theorem finset_normal {G : Type*} [Group G] {Index : Type*}
    (factors : Index → Subgroup G) (hnormal : ∀ index, (factors index).Normal)
    (indices : Finset Index) : (indices.sup factors).Normal := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa only [Finset.sup_empty] using (inferInstance : (⊥ : Subgroup G).Normal)
  | @insert index remaining _ hinduction =>
      rw [Finset.sup_insert]
      let : (factors index).Normal := hnormal index
      let : (remaining.sup factors).Normal := hinduction
      infer_instance

theorem finset_fixed_sup {G : Type*} [Group G] {Index : Type*}
    (factors : Index → Subgroup G) (hnormal : ∀ index, (factors index).Normal)
    (hindependent : iSupIndep factors) (automorphism : MulAut G)
    (hinvariant : ∀ index, (factors index).map automorphism.toMonoidHom = factors index)
    (indices : Finset Index) :
    indices.sup factors ⊓ FixedCommutingProduct.fixedSubgroup automorphism =
      indices.sup (fun index => factors index ⊓ FixedCommutingProduct.fixedSubgroup automorphism) := by
  classical
  have hmapSup : ∀ collection : Finset Index,
      (collection.sup factors).map automorphism.toMonoidHom = collection.sup factors := by
    intro collection
    induction collection using Finset.induction_on with
    | empty => simp only [Finset.sup_empty, Subgroup.map_bot]
    | @insert another smaller _ hsmaller =>
        rw [Finset.sup_insert, Subgroup.map_sup, hinvariant, hsmaller]
  induction indices using Finset.induction_on with
  | empty => simp only [Finset.sup_empty, bot_inf_eq]
  | @insert index remaining hnotMem hinduction =>
      rw [Finset.sup_insert, Finset.sup_insert]
      let : (factors index).Normal := hnormal index
      have hdisjoint : Disjoint (factors index) (remaining.sup factors) := by
        apply (iSupIndep_def.mp hindependent index).mono_right
        apply Finset.sup_le
        intro other hother
        exact le_iSup_of_le other (le_iSup_of_le (by
          intro heq
          exact hnotMem (heq ▸ hother)) le_rfl)
      rw [FixedCommutingProduct.fixed_sup_of_disjoint (factors index) (remaining.sup factors)
        hdisjoint automorphism (hinvariant index) (hmapSup remaining), hinduction]

end CFSG.ComponentClassification.CenterlessCommutingFamily
