module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.BlockAtoms
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.BlockResidues

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

noncomputable def subrepresentationTransport {field : Type*} [Field field]
    {leftGroup rightGroup : Type*} [Group leftGroup] [Group rightGroup]
    (equivalence : leftGroup ≃* rightGroup) {space : Type*}
    [AddCommGroup space] [Module field space]
    (representation : Representation field rightGroup space) :
    Subrepresentation (representation.comp equivalence.toMonoidHom) ≃o Subrepresentation representation where
  toFun subrepresentation := {
    toSubmodule := subrepresentation.toSubmodule
    apply_mem_toSubmodule element := by
      intro vector hvector
      have hstable := subrepresentation.apply_mem_toSubmodule (equivalence.symm element) hvector
      change representation (equivalence (equivalence.symm element)) vector ∈
        subrepresentation.toSubmodule at hstable
      rw [equivalence.apply_symm_apply] at hstable
      exact hstable
  }
  invFun subrepresentation := {
    toSubmodule := subrepresentation.toSubmodule
    apply_mem_toSubmodule element := subrepresentation.apply_mem_toSubmodule (equivalence element)
  }
  left_inv _ := Subrepresentation.ext rfl
  right_inv _ := Subrepresentation.ext rfl
  map_rel_iff' := Iff.rfl

theorem irreducible_comp_equiv {field : Type*} [Field field]
    {leftGroup rightGroup : Type*} [Group leftGroup] [Group rightGroup]
    (equivalence : leftGroup ≃* rightGroup) {space : Type*}
    [AddCommGroup space] [Module field space]
    (representation : Representation field rightGroup space) [representation.IsIrreducible] :
    Representation.IsIrreducible (representation.comp equivalence.toMonoidHom) :=
  (subrepresentationTransport equivalence representation).isSimpleOrder

theorem irr_comp_equiv {leftGroup rightGroup : Type*} [Group leftGroup] [Group rightGroup]
    (equivalence : leftGroup ≃* rightGroup) {character : rightGroup → ℂ}
    (hcharacter : character ∈ BlocksIrr rightGroup) :
    (character ∘ equivalence) ∈ BlocksIrr leftGroup := by
  obtain ⟨space, _, _, _, representation, hirreducible, rfl⟩ := hcharacter
  let : representation.IsIrreducible := hirreducible
  exact ⟨space, inferInstance, inferInstance, inferInstance,
    representation.comp equivalence.toMonoidHom, irreducible_comp_equiv equivalence representation, rfl⟩

theorem centralChar_comp_equiv {leftGroup rightGroup : Type*} [Group leftGroup] [Group rightGroup]
    [Finite leftGroup] [Finite rightGroup] (equivalence : leftGroup ≃* rightGroup)
    (character coefficients : rightGroup → ℂ) :
    BlocksCentralChar (character ∘ equivalence) (coefficients ∘ equivalence) =
      BlocksCentralChar character coefficients := by
  classical
  let : Fintype leftGroup := Fintype.ofFinite _
  let : Fintype rightGroup := Fintype.ofFinite _
  simp only [BlocksCentralChar, Function.comp_apply, map_one, finsum_eq_sum_of_fintype]
  congr 1
  exact Fintype.sum_equiv equivalence.toEquiv _ _ (fun _ => rfl)

theorem centralR_comp_equiv {leftGroup rightGroup : Type*} [Group leftGroup] [Group rightGroup]
    (m : Ideal BlocksAlgInt) (equivalence : leftGroup ≃* rightGroup)
    {coefficients : rightGroup → ℂ} (hcoefficients : BlocksIsCentralR m coefficients) :
    BlocksIsCentralR m (coefficients ∘ equivalence) := by
  refine ⟨fun element => hcoefficients.1 (equivalence element), ?_⟩
  intro element conjugator
  simp only [Function.comp_apply, map_mul, map_inv, hcoefficients.2]

theorem mem_blockOf_comp_equiv (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {leftGroup rightGroup : Type} [Group leftGroup] [Group rightGroup]
    [Finite leftGroup] [Finite rightGroup] (equivalence : leftGroup ≃* rightGroup)
    {left right : rightGroup → ℂ} (hleft : left ∈ BlocksIrr rightGroup)
    (hsame : right ∈ BlocksBlockOf m rightGroup left) :
    (right ∘ equivalence) ∈ BlocksBlockOf m leftGroup (left ∘ equivalence) := by
  apply mem_blockOf_of_centralChar_congr m hm leftGroup
    (irr_comp_equiv equivalence hleft) (irr_comp_equiv equivalence hsame.1)
  intro coefficients hcoefficients
  have hcongr := sameBlock_centralChar_congr m hm rightGroup hleft hsame
    (centralR_comp_equiv m equivalence.symm hcoefficients)
  have hright := centralChar_comp_equiv equivalence right (coefficients ∘ equivalence.symm)
  have hleftScalar := centralChar_comp_equiv equivalence left (coefficients ∘ equivalence.symm)
  have hcoeff : (coefficients ∘ equivalence.symm) ∘ equivalence = coefficients := by
    ext element
    simp only [Function.comp_apply, MulEquiv.symm_apply_apply]
  rw [hcoeff] at hright hleftScalar
  rw [hright, hleftScalar]
  exact hcongr

theorem principal_comp_equiv (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {leftGroup rightGroup : Type} [Group leftGroup] [Group rightGroup]
    [Finite leftGroup] [Finite rightGroup] (equivalence : leftGroup ≃* rightGroup)
    {character : rightGroup → ℂ} (hcharacter : character ∈ BlocksPrincipalBlock m rightGroup) :
    (character ∘ equivalence) ∈ BlocksPrincipalBlock m leftGroup := by
  exact mem_blockOf_comp_equiv m hm equivalence (trivial_mem_irr rightGroup) hcharacter

theorem principal_comp_equiv_iff (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {leftGroup rightGroup : Type} [Group leftGroup] [Group rightGroup]
    [Finite leftGroup] [Finite rightGroup] (equivalence : leftGroup ≃* rightGroup)
    (character : rightGroup → ℂ) :
    (character ∘ equivalence) ∈ BlocksPrincipalBlock m leftGroup ↔
      character ∈ BlocksPrincipalBlock m rightGroup := by
  constructor
  · intro hcharacter
    have htransport := principal_comp_equiv m hm equivalence.symm hcharacter
    have hequal : (character ∘ equivalence) ∘ equivalence.symm = character := by
      ext element
      simp only [Function.comp_apply, equivalence.apply_symm_apply]
    rw [hequal] at htransport
    exact htransport
  · exact principal_comp_equiv m hm equivalence

theorem principalIdempotent_comp_equiv (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {leftGroup rightGroup : Type} [Group leftGroup] [Group rightGroup]
    [Finite leftGroup] [Finite rightGroup] (equivalence : leftGroup ≃* rightGroup) :
    BlocksIdempotentCoeff rightGroup (BlocksPrincipalBlock m rightGroup) ∘ equivalence =
      BlocksIdempotentCoeff leftGroup (BlocksPrincipalBlock m leftGroup) := by
  classical
  have hleft := block_admissible m hm leftGroup (principal_isBlock m leftGroup)
  have hright := block_admissible m hm rightGroup (principal_isBlock m rightGroup)
  apply sub_eq_zero.mp
  apply centralChar_separates leftGroup
  · intro element conjugator
    simp only [Pi.sub_apply,
      (centralR_comp_equiv m equivalence (idempotentCoeff_central m rightGroup hright)).2 element conjugator,
      idempotentCoeff_conj hleft.1]
  · intro character hcharacter
    rw [centralChar_sub, centralChar_idempotentCoeff hleft.1 hcharacter]
    have htransport := centralChar_comp_equiv equivalence
      (character ∘ equivalence.symm)
      (BlocksIdempotentCoeff rightGroup (BlocksPrincipalBlock m rightGroup))
    have hequal : (character ∘ equivalence.symm) ∘ equivalence = character := by
      ext element
      simp only [Function.comp_apply, equivalence.symm_apply_apply]
    rw [hequal, centralChar_idempotentCoeff hright.1 (irr_comp_equiv equivalence.symm hcharacter),
      principal_comp_equiv_iff m hm equivalence.symm] at htransport
    rw [htransport]
    by_cases hmember : character ∈ BlocksPrincipalBlock m leftGroup <;>
      simp only [hmember, ↓reduceIte, sub_self]

end CFSG.BrauerThirdMainTheorem.Helpers
