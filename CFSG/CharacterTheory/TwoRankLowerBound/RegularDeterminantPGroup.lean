module

public import CFSG.CharacterTheory.TwoRankLowerBound.GroupAlgebraUnitResidue
public import CFSG.CharacterTheory.TwoRankLowerBound.PGroupInvariantSum

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

def groupRightTranslationHom (group : Type*) [Group group] : group →* Equiv.Perm group where
  toFun := fun element => Equiv.mulRight element⁻¹
  map_one' := by
    ext member
    simp
  map_mul' := by
    intro left right
    ext member
    simp only [Equiv.Perm.mul_apply, Equiv.coe_mulRight, mul_inv_rev]
    group

theorem p_group_field_hom_eq_one {field group : Type*} [Field field] [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] [CharP field prime] (hgroup : IsPGroup prime group)
    (homomorphism : group →* field) (element : group) : homomorphism element = 1 := by
  obtain ⟨exponent, hcard⟩ := hgroup.exists_card_eq
  have hpower : homomorphism element ^ (prime ^ exponent) = 1 := by
    rw [← map_pow, ← hcard, pow_card_eq_one', map_one]
  have hzero : (homomorphism element - 1) ^ (prime ^ exponent) = 0 := by
    rw [sub_pow_char_pow, hpower, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (Nat.ne_of_gt (Nat.pow_pos (Fact.out : prime.Prime).pos))).mp hzero)

theorem groupAlgebra_p_group_leftMultiplicationDet {field group : Type*}
    [Field field] [Group group] [Fintype group]
    (prime : ℕ) [Fact prime.Prime] [CharP field prime] (hgroup : IsPGroup prime group)
    (value : MonoidAlgebra field group) :
    LinearMap.det (Algebra.lmul field (MonoidAlgebra field group) value) =
      groupAlgebraAugmentation field group value ^ (Nat.card group) := by
  let translation := groupRightTranslationHom group
  let : MulAction group (Equiv.Perm group) :=
    MulAction.compHom (Equiv.Perm group) (MulAut.conj.comp translation)
  let weight : Equiv.Perm group → field := fun permutation =>
    ((Equiv.Perm.sign permutation : ℤˣ) : ℤ) *
      ∏ member : group, value.coeff (permutation member * member⁻¹)
  have haction : ∀ (element : group) (permutation : Equiv.Perm group) (member : group),
      (element • permutation) member = permutation (member * element) * element⁻¹ := by
    intro element permutation member
    change (translation element * permutation * (translation element)⁻¹) member = _
    rw [← map_inv]
    change (Equiv.mulRight element⁻¹ * permutation * Equiv.mulRight (element⁻¹)⁻¹) member = _
    simp only [Equiv.Perm.mul_apply, Equiv.coe_mulRight, inv_inv]
  have hinvariant : ∀ (element : group) (permutation : Equiv.Perm group),
      weight (element • permutation) = weight permutation := by
    intro element permutation
    change weight (translation element * permutation * (translation element)⁻¹) = weight permutation
    dsimp only [weight]
    have hsign : Equiv.Perm.sign (translation element * permutation * (translation element)⁻¹) =
        Equiv.Perm.sign permutation := by
      simp only [map_mul, map_inv]
      rw [mul_comm (Equiv.Perm.sign (translation element)), mul_assoc, mul_inv_cancel, mul_one]
    rw [hsign]
    congr 1
    apply Fintype.prod_equiv (Equiv.mulRight element)
    intro member
    change value.coeff
      ((translation element * permutation * (translation element)⁻¹) member * member⁻¹) =
      value.coeff (permutation (member * element) * (member * element)⁻¹)
    congr 1
    rw [← show element • permutation =
      translation element * permutation * (translation element)⁻¹ from rfl, haction]
    group
  have hfixed : ∀ permutation : Equiv.Perm group,
      permutation ∈ MulAction.fixedPoints group (Equiv.Perm group) ↔
        permutation = Equiv.mulLeft (permutation 1) := by
    intro permutation
    constructor
    · intro hmember
      ext member
      have hone := congrArg (fun operator : Equiv.Perm group => operator 1)
        (MulAction.mem_fixedPoints.mp hmember member)
      rw [haction, one_mul] at hone
      change permutation member = permutation 1 * member
      calc
        _ = (permutation member * member⁻¹) * member := by group
        _ = _ := by rw [hone]
    · intro hequal
      rw [MulAction.mem_fixedPoints]
      intro element
      ext member
      rw [haction]
      rw [hequal]
      change (permutation 1 * (member * element)) * element⁻¹ = permutation 1 * member
      group
  have hdet : LinearMap.det (Algebra.lmul field (MonoidAlgebra field group) value) =
      ∑ permutation, weight permutation := by
    rw [← LinearMap.det_toMatrix (MonoidAlgebra.basis group field), Matrix.det_apply']
    simp only [groupAlgebra_leftMultiplicationMatrix_apply]
    rfl
  rw [hdet, p_group_invariant_sum_fixedPoints prime hgroup weight hinvariant]
  have hsum : (∑ permutation : Equiv.Perm group,
      if permutation ∈ MulAction.fixedPoints group (Equiv.Perm group) then weight permutation else 0) =
        ∑ element : group, weight (Equiv.mulLeft element) := by
    let embedding : group ↪ Equiv.Perm group :=
      ⟨Equiv.mulLeft, fun left right hequal => by
        simpa only [Equiv.coe_mulLeft, mul_one] using congrArg (fun permutation => permutation 1) hequal⟩
    calc
      _ = ∑ permutation ∈ Finset.univ.map embedding,
          if permutation ∈ MulAction.fixedPoints group (Equiv.Perm group) then weight permutation else 0 := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro permutation _ hnot
        have hnotfixed : permutation ∉ MulAction.fixedPoints group (Equiv.Perm group) := by
          intro hmember
          apply hnot
          exact Finset.mem_map.mpr ⟨permutation 1, Finset.mem_univ _, (hfixed permutation).mp hmember |>.symm⟩
        rw [ite_eq_right hnotfixed]
      _ = _ := by
        rw [Finset.sum_map]
        apply Finset.sum_congr rfl
        intro element _
        have hmember : embedding element ∈ MulAction.fixedPoints group (Equiv.Perm group) := by
          apply (hfixed _).mpr
          change Equiv.mulLeft element = Equiv.mulLeft (element * 1)
          rw [mul_one]
        rw [ite_eq_left hmember]
        rfl
  rw [hsum]
  have hsign : ∀ element : group, ((Equiv.Perm.sign (Equiv.mulLeft element) : ℤ) : field) = 1 := by
    intro element
    let leftTranslation : group →* Equiv.Perm group :=
      { toFun := Equiv.mulLeft
        map_one' := Equiv.mulLeft_one
        map_mul' := Equiv.mulLeft_mul }
    let signHom : group →* field :=
      (Int.castRingHom field).toMonoidHom.comp
        ((Units.coeHom ℤ).comp (Equiv.Perm.sign.comp leftTranslation))
    exact p_group_field_hom_eq_one prime hgroup signHom element
  simp only [weight, hsign, one_mul, Equiv.coe_mulLeft, mul_inv_cancel_right,
    Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
  obtain ⟨exponent, hcard⟩ := hgroup.exists_card_eq
  let : ExpChar field prime := ExpChar.prime Fact.out
  rw [hcard, groupAlgebraAugmentation_sum, sum_pow_char_pow]

end CFSG.TwoRankLowerBound.Helpers
