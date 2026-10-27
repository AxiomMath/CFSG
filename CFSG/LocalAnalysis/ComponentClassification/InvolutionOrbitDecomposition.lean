module

public import CFSG.LocalAnalysis.ComponentClassification.CenterlessCommutingFamily

public section

namespace CFSG.ComponentClassification.InvolutionOrbitDecomposition

@[expose] def orbitFactor {G : Type*} [Group G] {Index : Type*}
    (factors : Index → Subgroup G) (permutation : Index → Index) (index : Index) : Subgroup G :=
  factors index ⊔ factors (permutation index)

@[expose] def fixedOrbit {G : Type*} [Group G] {Index : Type*}
    (factors : Index → Subgroup G) (permutation : Index → Index)
    (automorphism : MulAut G) (index : Index) : Subgroup G :=
  orbitFactor factors permutation index ⊓ FixedCommutingProduct.fixedSubgroup automorphism

theorem finset_invariant {G : Type*} [Group G] {Index : Type*}
    (factors : Index → Subgroup G) (permutation : Index → Index)
    (hpermutation : Function.Involutive permutation)
    (automorphism : MulAut G)
    (himages : ∀ index, (factors index).map automorphism.toMonoidHom = factors (permutation index))
    (indices : Finset Index) (hstable : ∀ index ∈ indices, permutation index ∈ indices) :
    (indices.sup factors).map automorphism.toMonoidHom = indices.sup factors := by
  classical
  have hmap : ∀ collection : Finset Index,
      (collection.sup factors).map automorphism.toMonoidHom =
        collection.sup (fun index => factors (permutation index)) := by
    intro collection
    induction collection using Finset.induction_on with
    | empty => simp only [Finset.sup_empty, Subgroup.map_bot]
    | @insert index remaining _ hinduction =>
        rw [Finset.sup_insert, Subgroup.map_sup, himages, hinduction, Finset.sup_insert]
  apply le_antisymm
  · rw [hmap]
    apply Finset.sup_le
    intro index hindex
    exact Finset.le_sup (hstable index hindex)
  · rw [hmap]
    apply Finset.sup_le
    intro index hindex
    have hle := Finset.le_sup (f := fun other => factors (permutation other))
      (hstable index hindex)
    rwa [hpermutation] at hle

theorem fixed_finset_sup {G : Type*} [Group G] {Index : Type*}
    (factors : Index → Subgroup G) (hnormal : ∀ index, (factors index).Normal)
    (hcenter : ∀ index, Subgroup.center (factors index) = ⊥)
    (hcommutes : Pairwise (fun first second => ⁅factors first, factors second⁆ = ⊥))
    (permutation : Index → Index) (hpermutation : Function.Involutive permutation)
    (automorphism : MulAut G)
    (himages : ∀ index, (factors index).map automorphism.toMonoidHom = factors (permutation index))
    (indices : Finset Index) (hstable : ∀ index ∈ indices, permutation index ∈ indices) :
    indices.sup factors ⊓ FixedCommutingProduct.fixedSubgroup automorphism =
      indices.sup (fixedOrbit factors permutation automorphism) := by
  classical
  revert hstable
  refine Finset.strongInductionOn indices ?_
  intro collection hinduction hstable
  by_cases hempty : collection = ∅
  · rw [hempty]
    simp only [Finset.sup_empty, bot_inf_eq]
  obtain ⟨index, hindex⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  let pair : Finset Index := {index, permutation index}
  let remainder := collection \ pair
  have hpairMem : ∀ other, other ∈ pair ↔ other = index ∨ other = permutation index := by
    intro other
    simp only [pair, Finset.mem_insert, Finset.mem_singleton]
  have hpairSubset : pair ⊆ collection := by
    intro other hother
    rcases (hpairMem other).mp hother with rfl | rfl
    · exact hindex
    · exact hstable index hindex
  have hpairStable : ∀ other ∈ pair, permutation other ∈ pair := by
    intro other hother
    rcases (hpairMem other).mp hother with rfl | rfl
    · exact (hpairMem _).mpr (Or.inr rfl)
    · rw [hpermutation]
      exact (hpairMem _).mpr (Or.inl rfl)
  have hremainderStable : ∀ other ∈ remainder, permutation other ∈ remainder := by
    intro other hother
    obtain ⟨hcollection, hnotPair⟩ := Finset.mem_sdiff.mp hother
    refine Finset.mem_sdiff.mpr ⟨hstable other hcollection, ?_⟩
    intro himagePair
    rcases (hpairMem _).mp himagePair with heq | heq
    · have horiginal : other = permutation index :=
        (hpermutation other).symm.trans (congrArg permutation heq)
      exact hnotPair ((hpairMem _).mpr (Or.inr horiginal))
    · exact hnotPair ((hpairMem _).mpr (Or.inl (hpermutation.injective heq)))
  have hremainderSmaller : remainder ⊂ collection := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
    intro heq
    have hmem : index ∈ remainder := heq.symm ▸ hindex
    exact (Finset.mem_sdiff.mp hmem).2 ((hpairMem _).mpr (Or.inl rfl))
  have hdisjoint : Disjoint pair remainder := by
    apply Finset.disjoint_left.mpr
    intro other hpair hremainder
    exact (Finset.mem_sdiff.mp hremainder).2 hpair
  have hcover : pair ∪ remainder = collection := by
    ext other
    constructor
    · intro hother
      rcases Finset.mem_union.mp hother with hpair | hremainder
      · exact hpairSubset hpair
      · exact (Finset.mem_sdiff.mp hremainder).1
    · intro hother
      by_cases hpair : other ∈ pair
      · exact Finset.mem_union.mpr (Or.inl hpair)
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hother, hpair⟩))
  let : (pair.sup factors).Normal := CenterlessCommutingFamily.finset_normal factors hnormal pair
  have hfixedDecomposition : collection.sup factors ⊓ FixedCommutingProduct.fixedSubgroup automorphism =
      (pair.sup factors ⊓ FixedCommutingProduct.fixedSubgroup automorphism) ⊔
        (remainder.sup factors ⊓ FixedCommutingProduct.fixedSubgroup automorphism) := by
    conv_lhs => rw [← hcover, Finset.sup_union]
    exact FixedCommutingProduct.fixed_sup_of_disjoint _ _
      (CenterlessCommutingFamily.finset_disjoint_sup factors hnormal hcenter hcommutes pair remainder hdisjoint)
      automorphism (finset_invariant factors permutation hpermutation automorphism himages pair hpairStable)
        (finset_invariant factors permutation hpermutation automorphism himages remainder hremainderStable)
  apply le_antisymm
  · rw [hfixedDecomposition, hinduction remainder hremainderSmaller hremainderStable]
    apply sup_le
    · have hle := Finset.le_sup (f := fixedOrbit factors permutation automorphism) hindex
      simpa only [pair, Finset.sup_insert, Finset.sup_singleton, fixedOrbit, orbitFactor] using hle
    · apply Finset.sup_le
      intro other hother
      exact Finset.le_sup (Finset.mem_sdiff.mp hother).1
  · apply Finset.sup_le
    intro other hother
    apply inf_le_inf_right
    exact sup_le (Finset.le_sup hother) (Finset.le_sup (hstable other hother))

theorem fixed_iSup {G : Type*} [Group G] {Index : Type*} [Fintype Index]
    (factors : Index → Subgroup G) (hnormal : ∀ index, (factors index).Normal)
    (hcenter : ∀ index, Subgroup.center (factors index) = ⊥)
    (hcommutes : Pairwise (fun first second => ⁅factors first, factors second⁆ = ⊥))
    (permutation : Index → Index) (hpermutation : Function.Involutive permutation)
    (automorphism : MulAut G)
    (himages : ∀ index, (factors index).map automorphism.toMonoidHom = factors (permutation index)) :
    (⨆ index, factors index) ⊓ FixedCommutingProduct.fixedSubgroup automorphism =
      ⨆ index, fixedOrbit factors permutation automorphism index := by
  classical
  simpa only [Finset.sup_univ_eq_iSup] using fixed_finset_sup factors hnormal hcenter hcommutes
    permutation hpermutation automorphism himages Finset.univ (fun _ _ => Finset.mem_univ _)

end CFSG.ComponentClassification.InvolutionOrbitDecomposition
