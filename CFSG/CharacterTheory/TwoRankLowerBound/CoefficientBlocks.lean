module

public import CFSG.CharacterTheory.TwoRankLowerBound.CentralIdempotentSpectral

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] def groupAlgebraCoefficientSubring {G : Type*} [Group G] (coefficientRing : Subring ℂ) :
    Subring (MonoidAlgebra ℂ G) where
  carrier := {algebraElement | ∀ element : G, algebraElement.coeff element ∈ coefficientRing}
  zero_mem' := by simp
  one_mem' := by
    intro element
    change (MonoidAlgebra.single (1 : G) (1 : ℂ)).coeff element ∈ coefficientRing
    simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs
    · exact coefficientRing.one_mem
    · exact coefficientRing.zero_mem
  add_mem' := by
    intro left right hleft hright element
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact coefficientRing.add_mem (hleft element) (hright element)
  neg_mem' := by
    intro algebraElement hmember element
    simp only [MonoidAlgebra.coeff_neg, Finsupp.neg_apply]
    exact coefficientRing.neg_mem (hmember element)
  mul_mem' := by
    intro left right hleft hright element
    rw [MonoidAlgebra.coeff_mul_apply_left]
    exact coefficientRing.sum_mem (fun member _ =>
      coefficientRing.mul_mem (hleft member) (hright (member⁻¹ * element)))

@[expose] def characterSubsetAdmissible {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ)
    (support : Finset basis.index) : Prop :=
  characterSubsetIdempotent basis support ∈ groupAlgebraCoefficientSubring coefficientRing

@[expose] def sameCoefficientBlock {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ)
    (left right : basis.index) : Prop :=
  ∀ support : Finset basis.index, characterSubsetAdmissible basis coefficientRing support →
    (left ∈ support ↔ right ∈ support)

@[expose] def coefficientCharacterSpace {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (support : Finset basis.index) :
    Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ ((fun label => (basis.representation label).character) '' (support : Set basis.index))

@[expose] def coefficientVirtualLattice {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (support : Finset basis.index) :
    Submodule ℤ (G → ℂ) :=
  Submodule.span ℤ ((fun label => (basis.representation label).character) '' (support : Set basis.index))

@[expose] noncomputable def coefficientBlock {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ)
    (label : basis.index) : Finset basis.index :=
  Finset.univ.filter (sameCoefficientBlock basis coefficientRing label)

theorem sameCoefficientBlock_refl {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ)
    (label : basis.index) : sameCoefficientBlock basis coefficientRing label label := by
  intro support _
  rfl

theorem sameCoefficientBlock_symm {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ)
    {left right : basis.index} (hequal : sameCoefficientBlock basis coefficientRing left right) :
    sameCoefficientBlock basis coefficientRing right left := by
  intro support hadmissible
  exact (hequal support hadmissible).symm

theorem sameCoefficientBlock_trans {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ)
    {left middle right : basis.index}
    (hfirst : sameCoefficientBlock basis coefficientRing left middle)
    (hsecond : sameCoefficientBlock basis coefficientRing middle right) :
    sameCoefficientBlock basis coefficientRing left right := by
  intro support hadmissible
  exact (hfirst support hadmissible).trans (hsecond support hadmissible)

theorem coefficientBlock_mem_iff {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ)
    (left right : basis.index) :
    right ∈ coefficientBlock basis coefficientRing left ↔
      sameCoefficientBlock basis coefficientRing left right := by
  simp only [coefficientBlock, Finset.mem_filter, Finset.mem_univ, true_and]

theorem coefficientBlock_self_mem {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ)
    (label : basis.index) : label ∈ coefficientBlock basis coefficientRing label := by
  exact (coefficientBlock_mem_iff _ _ _ _).mpr (sameCoefficientBlock_refl _ _ _)

theorem characterSubsetAdmissible_univ {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ) :
    characterSubsetAdmissible basis coefficientRing Finset.univ := by
  change characterSubsetIdempotent basis Finset.univ ∈ _
  rw [characterSubsetIdempotent_univ]
  exact (groupAlgebraCoefficientSubring coefficientRing).one_mem

theorem characterSubsetAdmissible_compl {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ)
    (support : Finset basis.index) (hadmissible : characterSubsetAdmissible basis coefficientRing support) :
    characterSubsetAdmissible basis coefficientRing supportᶜ := by
  change characterSubsetIdempotent basis supportᶜ ∈ _
  rw [characterSubsetIdempotent_compl]
  exact (groupAlgebraCoefficientSubring coefficientRing).sub_mem
    (groupAlgebraCoefficientSubring coefficientRing).one_mem hadmissible

theorem characterSubsetAdmissible_inter {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ)
    (left right : Finset basis.index)
    (hleft : characterSubsetAdmissible basis coefficientRing left)
    (hright : characterSubsetAdmissible basis coefficientRing right) :
    characterSubsetAdmissible basis coefficientRing (left ∩ right) := by
  change characterSubsetIdempotent basis (left ∩ right) ∈ _
  rw [characterSubsetIdempotent_inter]
  exact (groupAlgebraCoefficientSubring coefficientRing).mul_mem hleft hright

theorem characterSubsetAdmissible_finite_intersection {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ)
    (family : Finset (Finset basis.index))
    (hadmissible : ∀ support ∈ family, characterSubsetAdmissible basis coefficientRing support) :
    characterSubsetAdmissible basis coefficientRing
      (Finset.univ.filter (fun label => ∀ support ∈ family, label ∈ support)) := by
  induction family using Finset.induction_on with
  | empty =>
    simpa using characterSubsetAdmissible_univ basis coefficientRing
  | @insert support family hnot hinduction =>
    have hequal : Finset.univ.filter (fun label => ∀ member ∈ insert support family, label ∈ member) =
        support ∩ Finset.univ.filter (fun label => ∀ member ∈ family, label ∈ member) := by
      ext label
      simp
    rw [hequal]
    apply characterSubsetAdmissible_inter
    · exact hadmissible support (Finset.mem_insert_self _ _)
    · exact hinduction (fun member hmember => hadmissible member (Finset.mem_insert_of_mem hmember))

theorem coefficientBlock_eq_admissible_intersection {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ)
    (label : basis.index) :
    coefficientBlock basis coefficientRing label = Finset.univ.filter
      (fun other => ∀ support : Finset basis.index,
        characterSubsetAdmissible basis coefficientRing support → label ∈ support → other ∈ support) := by
  ext other
  rw [coefficientBlock_mem_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hequal support hadmissible hmember
    exact (hequal support hadmissible).mp hmember
  · intro htests support hadmissible
    constructor
    · exact htests support hadmissible
    · intro hmember
      by_contra hnot
      have hotherNot := htests supportᶜ
        (characterSubsetAdmissible_compl _ _ _ hadmissible) (Finset.mem_compl.mpr hnot)
      exact (Finset.mem_compl.mp hotherNot) hmember

theorem coefficientBlock_admissible {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ)
    (label : basis.index) : characterSubsetAdmissible basis coefficientRing
      (coefficientBlock basis coefficientRing label) := by
  let family : Finset (Finset basis.index) :=
    Finset.univ.filter (fun support => characterSubsetAdmissible basis coefficientRing support ∧ label ∈ support)
  have hintersection := characterSubsetAdmissible_finite_intersection basis coefficientRing family
    (fun support hmember => (Finset.mem_filter.mp hmember).2.1)
  have hequal : coefficientBlock basis coefficientRing label =
      Finset.univ.filter (fun other => ∀ support ∈ family, other ∈ support) := by
    rw [coefficientBlock_eq_admissible_intersection]
    ext other
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, family]
    constructor
    · intro htests support hmember
      exact htests support hmember.1 hmember.2
    · intro htests support hadmissible hmember
      exact htests support ⟨hadmissible, hmember⟩
  rw [hequal]
  exact hintersection

theorem coefficientBlock_eq_of_mem {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ)
    {left right : basis.index} (hmember : right ∈ coefficientBlock basis coefficientRing left) :
    coefficientBlock basis coefficientRing right = coefficientBlock basis coefficientRing left := by
  have hequal := (coefficientBlock_mem_iff _ _ _ _).mp hmember
  ext label
  simp only [coefficientBlock_mem_iff]
  constructor
  · intro hright
    exact sameCoefficientBlock_trans basis coefficientRing hequal hright
  · intro hleft
    exact sameCoefficientBlock_trans basis coefficientRing
      (sameCoefficientBlock_symm basis coefficientRing hequal) hleft

theorem coefficientBlock_disjoint_or_eq {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ)
    (left right : basis.index) :
    Disjoint (coefficientBlock basis coefficientRing left) (coefficientBlock basis coefficientRing right) ∨
      coefficientBlock basis coefficientRing left = coefficientBlock basis coefficientRing right := by
  by_cases hdisjoint : Disjoint (coefficientBlock basis coefficientRing left)
      (coefficientBlock basis coefficientRing right)
  · exact Or.inl hdisjoint
  · right
    obtain ⟨label, hleft, hright⟩ := Finset.not_disjoint_iff.mp hdisjoint
    exact (coefficientBlock_eq_of_mem basis coefficientRing hleft).symm.trans
      (coefficientBlock_eq_of_mem basis coefficientRing hright)

theorem coefficientBlock_subset_admissible {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ)
    (support : Finset basis.index) (hadmissible : characterSubsetAdmissible basis coefficientRing support)
    (label : basis.index) (hlabel : label ∈ support) :
    coefficientBlock basis coefficientRing label ⊆ support := by
  intro other hother
  exact ((coefficientBlock_mem_iff _ _ _ _).mp hother support hadmissible).mp hlabel

theorem characterSubsetAdmissible_union {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ)
    (left right : Finset basis.index)
    (hleft : characterSubsetAdmissible basis coefficientRing left)
    (hright : characterSubsetAdmissible basis coefficientRing right) :
    characterSubsetAdmissible basis coefficientRing (left ∪ right) := by
  change characterSubsetIdempotent basis (left ∪ right) ∈ _
  rw [characterSubsetIdempotent_union]
  exact (groupAlgebraCoefficientSubring coefficientRing).sub_mem
    ((groupAlgebraCoefficientSubring coefficientRing).add_mem hleft hright)
    (characterSubsetAdmissible_inter basis coefficientRing left right hleft hright)

theorem characterSubsetAdmissible_empty {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ) :
    characterSubsetAdmissible basis coefficientRing ∅ := by
  change characterSubsetIdempotent basis ∅ ∈ _
  rw [characterSubsetIdempotent_empty]
  exact (groupAlgebraCoefficientSubring coefficientRing).zero_mem

theorem characterSubsetAdmissible_biUnion {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ)
    (family : Finset (Finset basis.index))
    (hadmissible : ∀ support ∈ family, characterSubsetAdmissible basis coefficientRing support) :
    characterSubsetAdmissible basis coefficientRing (family.biUnion id) := by
  induction family using Finset.induction_on with
  | empty => exact characterSubsetAdmissible_empty basis coefficientRing
  | @insert support family hnot hinduction =>
    rw [Finset.biUnion_insert]
    exact characterSubsetAdmissible_union basis coefficientRing support _
      (hadmissible support (Finset.mem_insert_self _ _))
      (hinduction (fun member hmember => hadmissible member (Finset.mem_insert_of_mem hmember)))

theorem characterSubsetAdmissible_iff_union_blocks {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ)
    (support : Finset basis.index) :
    characterSubsetAdmissible basis coefficientRing support ↔
      ∀ label ∈ support, coefficientBlock basis coefficientRing label ⊆ support := by
  constructor
  · exact fun hadmissible label hlabel =>
      coefficientBlock_subset_admissible basis coefficientRing support hadmissible label hlabel
  · intro hclosed
    have hequal : support = (support.image (coefficientBlock basis coefficientRing)).biUnion id := by
      ext label
      simp only [Finset.mem_biUnion, Finset.mem_image, id_eq, exists_exists_and_eq_and]
      constructor
      · intro hlabel
        exact ⟨label, hlabel, coefficientBlock_self_mem basis coefficientRing label⟩
      · rintro ⟨member, hmember, hlabel⟩
        exact hclosed member hmember hlabel
    rw [hequal]
    apply characterSubsetAdmissible_biUnion
    intro block hmember
    obtain ⟨label, _, rfl⟩ := Finset.mem_image.mp hmember
    exact coefficientBlock_admissible basis coefficientRing label

theorem coefficientBlock_admissible_subset_empty_or_eq {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ)
    (label : basis.index) (support : Finset basis.index)
    (hadmissible : characterSubsetAdmissible basis coefficientRing support)
    (hsubset : support ⊆ coefficientBlock basis coefficientRing label) :
    support = ∅ ∨ support = coefficientBlock basis coefficientRing label := by
  rcases support.eq_empty_or_nonempty with hempty | ⟨member, hmember⟩
  · exact Or.inl hempty
  · right
    apply Finset.Subset.antisymm hsubset
    rw [← coefficientBlock_eq_of_mem basis coefficientRing (hsubset hmember)]
    exact coefficientBlock_subset_admissible basis coefficientRing support hadmissible member hmember

theorem admissible_atom_iff_coefficientBlock {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ)
    (support : Finset basis.index) (hadmissible : characterSubsetAdmissible basis coefficientRing support)
    (hnonempty : support.Nonempty) :
    (∀ subset : Finset basis.index, characterSubsetAdmissible basis coefficientRing subset →
      subset ⊆ support → subset = ∅ ∨ subset = support) ↔
      ∃ label : basis.index, support = coefficientBlock basis coefficientRing label := by
  constructor
  · intro hatom
    obtain ⟨label, hlabel⟩ := hnonempty
    rcases hatom (coefficientBlock basis coefficientRing label)
      (coefficientBlock_admissible basis coefficientRing label)
      (coefficientBlock_subset_admissible basis coefficientRing support hadmissible label hlabel) with
      hempty | hequal
    · have hmember := coefficientBlock_self_mem basis coefficientRing label
      rw [hempty] at hmember
      exact False.elim (Finset.notMem_empty _ hmember)
    · exact ⟨label, hequal.symm⟩
  · rintro ⟨label, rfl⟩ subset hsubset hle
    exact coefficientBlock_admissible_subset_empty_or_eq basis coefficientRing label subset hsubset hle

end CFSG.TwoRankLowerBound.Helpers
