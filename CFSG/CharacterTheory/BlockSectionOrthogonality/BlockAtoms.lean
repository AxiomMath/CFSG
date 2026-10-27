module

public import CFSG.CharacterTheory.BlockSectionOrthogonality.GroupAlgebraSpectral
public import CFSG.CharacterTheory.BlockSectionOrthogonality.LocalCoefficients

public section

open CFSG
namespace CFSG.BlockSectionOrthogonality.Helpers

theorem localRing_sub_mem (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {left right : ℂ} (hLeft : left ∈ BlocksLocalRing m)
    (hRight : right ∈ BlocksLocalRing m) : left - right ∈ BlocksLocalRing m := by
  rw [sub_eq_add_neg]
  exact localRing_add_mem m hm hLeft (localRing_neg_mem m hRight)

theorem localRing_sum_mem (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {index : Type*} (indices : Finset index) (value : index → ℂ)
    (hValue : ∀ index ∈ indices, value index ∈ BlocksLocalRing m) :
    ∑ index ∈ indices, value index ∈ BlocksLocalRing m := by
  exact (localCoefficientSubring m hm).sum_mem hValue

theorem groupAlgebra_mul_coeff_mem_localRing (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {G : Type} [Group G] [Fintype G] (left right : MonoidAlgebra ℂ G)
    (hLeft : ∀ element, left.coeff element ∈ BlocksLocalRing m)
    (hRight : ∀ element, right.coeff element ∈ BlocksLocalRing m) (element : G) :
    (left * right).coeff element ∈ BlocksLocalRing m := by
  classical
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp)]
  apply localRing_sum_mem m hm
  intro index hIndex
  exact localRing_mul_mem m hm (hLeft index) (hRight (index⁻¹ * element))

theorem admissible_all (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type) [Group G] [Finite G] : BlocksAdmissible m G (BlocksIrr G) := by
  classical
  let := Fintype.ofFinite G
  refine ⟨Set.Subset.refl _, ?_⟩
  intro element
  rw [← setIdempotent_coeff _ (irreducibles_finite G), setIdempotent_all]
  change (MonoidAlgebra.single (1 : G) (1 : ℂ)).coeff element ∈ _
  change (Finsupp.single (1 : G) (1 : ℂ)) element ∈ _
  rw [Finsupp.single_apply]
  split_ifs
  · exact localRing_one_mem m hm
  · exact localRing_zero_mem m hm

theorem admissible_inter (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type) [Group G] [Finite G] {left right : Set (G → ℂ)}
    (hLeft : BlocksAdmissible m G left) (hRight : BlocksAdmissible m G right) :
    BlocksAdmissible m G (left ∩ right) := by
  classical
  let := Fintype.ofFinite G
  have hLeftFinite := (irreducibles_finite G).subset hLeft.1
  have hRightFinite := (irreducibles_finite G).subset hRight.1
  refine ⟨fun _ hMember => hLeft.1 hMember.1, ?_⟩
  intro element
  rw [← setIdempotent_coeff _ (hLeftFinite.inter_of_left _),
    setIdempotent_inter _ _ hLeftFinite hRightFinite hLeft.1 hRight.1]
  apply groupAlgebra_mul_coeff_mem_localRing m hm
  · intro index
    rw [setIdempotent_coeff]
    exact hLeft.2 index
  · intro index
    rw [setIdempotent_coeff]
    exact hRight.2 index

theorem admissible_complement (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type) [Group G] [Finite G] {characters : Set (G → ℂ)}
    (hCharacters : BlocksAdmissible m G characters) :
    BlocksAdmissible m G (BlocksIrr G \ characters) := by
  classical
  let := Fintype.ofFinite G
  have hFinite := (irreducibles_finite G).subset hCharacters.1
  refine ⟨fun _ hMember => hMember.1, ?_⟩
  intro element
  rw [← setIdempotent_coeff _ (irreducibles_finite G).sdiff,
    setIdempotent_diff _ _ (irreducibles_finite G) hFinite (Set.Subset.refl _) hCharacters.1,
    MonoidAlgebra.coeff_sub, Finsupp.sub_apply, setIdempotent_coeff, setIdempotent_coeff]
  exact localRing_sub_mem m hm ((admissible_all m hm G).2 element) (hCharacters.2 element)

theorem admissible_finiteIntersection (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type) [Group G] [Finite G] (family : Finset (Set (G → ℂ)))
    (hFamily : ∀ characters ∈ family, BlocksAdmissible m G characters) :
    BlocksAdmissible m G (BlocksIrr G ∩ ⋂ characters ∈ family, characters) := by
  classical
  induction family using Finset.induction_on with
  | empty => simpa using admissible_all m hm G
  | @insert characters family hNotMember hInduction =>
    have hTail : ∀ subset ∈ family, BlocksAdmissible m G subset :=
      fun subset hMember => hFamily subset (Finset.mem_insert_of_mem hMember)
    have hHead := hFamily characters (Finset.mem_insert_self _ _)
    have hResult := admissible_inter m hm G (hInduction hTail) hHead
    convert hResult using 1
    ext character
    simp only [Set.mem_inter_iff, Set.mem_iInter, Finset.mem_insert]
    aesop

theorem blockOf_admissible (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type) [Group G] [Finite G] (character : G → ℂ)
    (hCharacter : character ∈ BlocksIrr G) :
    BlocksAdmissible m G (BlocksBlockOf m G character) := by
  classical
  let family : Set (Set (G → ℂ)) :=
    {characters | BlocksAdmissible m G characters ∧ character ∈ characters}
  have hFamilyFinite : family.Finite :=
    (irreducibles_finite G).powerset.subset (fun _ hMember => hMember.1.1)
  have hAdmissible := admissible_finiteIntersection m hm G hFamilyFinite.toFinset
    (fun characters hMember => (hFamilyFinite.mem_toFinset.mp hMember).1)
  have hEqual : BlocksBlockOf m G character =
      BlocksIrr G ∩ ⋂ characters ∈ hFamilyFinite.toFinset, characters := by
    ext member
    constructor
    · intro hMember
      refine ⟨hMember.1, ?_⟩
      simp only [Set.mem_iInter]
      intro characters hSet
      have hSet' := hFamilyFinite.mem_toFinset.mp hSet
      exact (hMember.2 characters hSet'.1).mp hSet'.2
    · intro hMember
      refine ⟨hMember.1, ?_⟩
      intro characters hSet
      constructor
      · intro hContains
        have hSetMember : characters ∈ hFamilyFinite.toFinset :=
          hFamilyFinite.mem_toFinset.mpr ⟨hSet, hContains⟩
        exact Set.mem_iInter.mp (Set.mem_iInter.mp hMember.2 characters) hSetMember
      · intro hContains
        by_contra hNotContains
        have hComplement := admissible_complement m hm G hSet
        have hSetMember : BlocksIrr G \ characters ∈ hFamilyFinite.toFinset :=
          hFamilyFinite.mem_toFinset.mpr ⟨hComplement, hCharacter, hNotContains⟩
        have hInComplement := Set.mem_iInter.mp
          (Set.mem_iInter.mp hMember.2 (BlocksIrr G \ characters)) hSetMember
        exact hInComplement.2 hContains
  rw [hEqual]
  exact hAdmissible

theorem block_admissible (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type) [Group G] [Finite G] {block : Set (G → ℂ)}
    (hBlock : BlocksIsBlock m G block) : BlocksAdmissible m G block := by
  rcases hBlock with ⟨character, hCharacter, rfl⟩
  exact blockOf_admissible m hm G character hCharacter

end CFSG.BlockSectionOrthogonality.Helpers
