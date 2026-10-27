module

public import CFSG.CharacterTheory.TwoRankLowerBound.CoefficientBlocks
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerInduction

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def characterSubsetProjection {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (support : Finset basis.index) :
    (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun := fun function => ∑ label ∈ support,
    characterPairing function (basis.representation label).character •
      (basis.representation label).character
  map_add' := by
    intro left right
    have hadd := (characterBasisComplexCoordinates basis).map_add left right
    funext element
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro label _
    have hcoordinate := congrFun hadd label
    change characterPairing (left + right) (basis.representation label).character =
      characterPairing left (basis.representation label).character +
        characterPairing right (basis.representation label).character at hcoordinate
    rw [hcoordinate, add_mul]
  map_smul' := by
    intro scalar function
    have hsmul := (characterBasisComplexCoordinates basis).map_smul scalar function
    funext element
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro label _
    have hcoordinate := congrFun hsmul label
    change characterPairing (scalar • function) (basis.representation label).character =
      scalar * characterPairing function (basis.representation label).character at hcoordinate
    rw [hcoordinate, mul_assoc]

theorem characterSubsetProjection_mem {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (support : Finset basis.index) (function : G → ℂ) :
    characterSubsetProjection basis support function ∈ coefficientCharacterSpace basis support := by
  apply Submodule.sum_mem
  intro label hmember
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨label, hmember, rfl⟩)

theorem characterSubsetProjection_character {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (support : Finset basis.index)
    (label : basis.index) (hmember : label ∈ support) :
    characterSubsetProjection basis support (basis.representation label).character =
      (basis.representation label).character := by
  change (∑ member ∈ support,
    characterPairing (basis.representation label).character (basis.representation member).character •
      (basis.representation member).character) = _
  rw [Finset.sum_eq_single label]
  · rw [characterPairing_irreducible _ _ (basis.irreducible label) (basis.irreducible label),
      ite_eq_left rfl, one_smul]
  · intro member _ hne
    rw [characterPairing_irreducible _ _ (basis.irreducible label) (basis.irreducible member),
      ite_eq_right (fun hequal => hne (basis.distinct hequal).symm), zero_smul]
  · exact fun hnot => (hnot hmember).elim

theorem characterSubsetProjection_identity {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (support : Finset basis.index)
    (function : G → ℂ) (hfunction : function ∈ coefficientCharacterSpace basis support) :
    characterSubsetProjection basis support function = function := by
  induction hfunction using Submodule.span_induction with
  | mem generator hmember =>
    obtain ⟨label, hlabel, rfl⟩ := hmember
    exact characterSubsetProjection_character basis support label hlabel
  | zero => exact (characterSubsetProjection basis support).map_zero
  | add left right _ _ hleft hright =>
    rw [map_add, hleft, hright]
  | smul scalar function _ hequal =>
    rw [map_smul, hequal]

@[expose] noncomputable def characterSubsetColumnKernel {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (support : Finset basis.index)
    (left right : G) : ℂ :=
  ∑ label ∈ support,
    (basis.representation label).character left * (basis.representation label).character right⁻¹

theorem characterSubsetProjection_kernel {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (support : Finset basis.index)
    (function : G → ℂ) (element : G) :
    characterSubsetProjection basis support function element =
      (Nat.card G : ℂ)⁻¹ * ∑ member,
        function member * characterSubsetColumnKernel basis support element member := by
  simp only [characterSubsetProjection, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, characterPairing,
    characterSubsetColumnKernel, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro member _
  apply Finset.sum_congr rfl
  intro label _
  ring

@[expose] noncomputable def characterFunctionMask {G : Type*} (domain : Set G) (function : G → ℂ) : G → ℂ :=
  fun element => if element ∈ domain then function element else 0

theorem characterSubsetProjection_mask_commute {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (support : Finset basis.index) (domain : Set G)
    (hkernel : ∀ left right : G, ¬ (left ∈ domain ↔ right ∈ domain) →
      characterSubsetColumnKernel basis support left right = 0) (function : G → ℂ) :
    characterSubsetProjection basis support (characterFunctionMask domain function) =
      characterFunctionMask domain (characterSubsetProjection basis support function) := by
  funext element
  rw [characterSubsetProjection_kernel]
  by_cases helement : element ∈ domain
  · rw [characterFunctionMask, ite_eq_left helement, characterSubsetProjection_kernel]
    congr 1
    apply Finset.sum_congr rfl
    intro member _
    by_cases hmember : member ∈ domain
    · rw [characterFunctionMask, ite_eq_left hmember]
    · rw [characterFunctionMask, ite_eq_right hmember,
        hkernel element member (fun hequal => hmember (hequal.mp helement))]
      simp only [mul_zero]
  · rw [characterFunctionMask, ite_eq_right helement]
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro member _
    by_cases hmember : member ∈ domain
    · rw [hkernel element member (fun hequal => helement (hequal.mpr hmember)), mul_zero]
    · rw [characterFunctionMask, ite_eq_right hmember, zero_mul]

theorem coefficientCharacterSpace_mask_mem {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (support : Finset basis.index) (domain : Set G)
    (hkernel : ∀ left right : G, ¬ (left ∈ domain ↔ right ∈ domain) →
      characterSubsetColumnKernel basis support left right = 0)
    (function : G → ℂ) (hfunction : function ∈ coefficientCharacterSpace basis support) :
    characterFunctionMask domain function ∈ coefficientCharacterSpace basis support := by
  rw [← characterSubsetProjection_identity basis support function hfunction,
    ← characterSubsetProjection_mask_commute basis support domain hkernel]
  exact characterSubsetProjection_mem basis support _

end CFSG.TwoRankLowerBound.Helpers
