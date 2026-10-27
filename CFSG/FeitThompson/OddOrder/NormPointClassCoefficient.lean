module

public import CFSG.FeitThompson.OddOrder.AffineFieldCentralizers
public import CFSG.FeitThompson.Representations.ClassSumsIntegerStructureConstants

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open SemidirectProduct

variable {F : Type*} [Field F] {U : Subgroup Fˣ} {p q m : ℕ}

def fieldAffinePointOne (F : Type*) [Field F] (U : Subgroup Fˣ) : fieldAffineGroup F U :=
  inl (Multiplicative.ofAdd (1 : F))

theorem fieldAffinePointOne_eq :
    fieldAffinePointOne F U = inl (Multiplicative.ofAdd (1 : F)) := (rfl)

theorem inl_ofAdd_injective :
    Function.Injective fun z : F => (inl (Multiplicative.ofAdd z) : fieldAffineGroup F U) :=
  fun _ _ h => Multiplicative.ofAdd.injective (inl_injective h)

theorem inl_ofAdd_mul_inl_ofAdd (z w : F) :
    (inl (Multiplicative.ofAdd z) : fieldAffineGroup F U) * inl (Multiplicative.ofAdd w)
      = inl (Multiplicative.ofAdd (z + w)) := by
  rw [← map_mul, ← ofAdd_add]

theorem fieldAffinePointOne_sq :
    fieldAffinePointOne F U ^ 2 = inl (Multiplicative.ofAdd (2 : F)) := by
  rw [fieldAffinePointOne_eq, sq, inl_ofAdd_mul_inl_ofAdd, one_add_one_eq_two]

theorem conj_inl_ofAdd (z : F) (h : fieldAffineGroup F U) :
    h⁻¹ * inl (Multiplicative.ofAdd z) * h
      = inl (Multiplicative.ofAdd (z * ((h.right : Fˣ) : F))) := by
  have hcomm : (inl h.left : fieldAffineGroup F U)⁻¹ * inl (Multiplicative.ofAdd z) * inl h.left
      = inl (Multiplicative.ofAdd z) := by
    rw [← map_inv, ← map_mul, ← map_mul, mul_assoc, mul_comm (Multiplicative.ofAdd z) h.left,
      inv_mul_cancel_left]
  conv_lhs => rw [← inl_left_mul_inr_right h]
  calc (inl h.left * inr h.right : fieldAffineGroup F U)⁻¹ * inl (Multiplicative.ofAdd z)
        * (inl h.left * inr h.right)
      = (inr h.right : fieldAffineGroup F U)⁻¹
          * ((inl h.left : fieldAffineGroup F U)⁻¹ * inl (Multiplicative.ofAdd z) * inl h.left)
          * inr h.right := by group
    _ = (inr h.right : fieldAffineGroup F U)⁻¹ * inl (Multiplicative.ofAdd z)
          * inr h.right := by rw [hcomm]
    _ = _ := inv_inr_mul_inl_mul_inr h.right z

theorem mem_conjugatesOf_fieldAffinePointOne {x : fieldAffineGroup F U} :
    x ∈ conjugatesOf (fieldAffinePointOne F U) ↔
      ∃ u ∈ U, x = inl (Multiplicative.ofAdd ((u : F))) := by
  constructor
  · rintro hx
    obtain ⟨c, hc⟩ := isConj_iff.1 hx
    refine ⟨((c⁻¹).right : Fˣ), (c⁻¹).right.2, ?_⟩
    have h := conj_inl_ofAdd (U := U) (1 : F) c⁻¹
    rw [one_mul] at h
    rw [← h, inv_inv, ← fieldAffinePointOne_eq, hc]
  · rintro ⟨u, hu, rfl⟩
    refine isConj_iff.2 ⟨(inr ⟨u, hu⟩ : fieldAffineGroup F U)⁻¹, ?_⟩
    have h := conj_inl_ofAdd (U := U) (1 : F) (inr ⟨u, hu⟩)
    rw [right_inr, one_mul, ← fieldAffinePointOne_eq] at h
    rw [← h, inv_inv]

def unitVals (U : Subgroup Fˣ) : Set F := Units.val '' (U : Set Fˣ)

@[simp] theorem mem_unitVals {a : F} : a ∈ unitVals U ↔ ∃ u ∈ U, (u : F) = a := by
  simp [unitVals]

theorem conjugatesOf_fieldAffinePointOne :
    conjugatesOf (fieldAffinePointOne F U)
      = (fun a : F => (inl (Multiplicative.ofAdd a) : fieldAffineGroup F U)) '' unitVals U := by
  ext x
  rw [mem_conjugatesOf_fieldAffinePointOne]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(u : F), ⟨u, hu, rfl⟩, rfl⟩
  · rintro ⟨a, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, rfl⟩

theorem ncard_conjugatesOf_fieldAffinePointOne :
    (conjugatesOf (fieldAffinePointOne F U)).ncard = Nat.card U := by
  rw [conjugatesOf_fieldAffinePointOne, Set.ncard_image_of_injective _ inl_ofAdd_injective,
    unitVals, Set.ncard_image_of_injective _ Units.val_injective]
  exact (Nat.card_coe_set_eq _).symm

def fieldAffineSquarePairs (F : Type*) [Field F] (U : Subgroup Fˣ) :
    Set (fieldAffineGroup F U × fieldAffineGroup F U) :=
  {P | P.1 ∈ conjugatesOf (fieldAffinePointOne F U) ∧
    P.2 ∈ conjugatesOf (fieldAffinePointOne F U) ∧
    P.1 * P.2 = fieldAffinePointOne F U ^ 2}

theorem mem_fieldAffineSquarePairs {x y : fieldAffineGroup F U} :
    (x, y) ∈ fieldAffineSquarePairs F U ↔
      x ∈ conjugatesOf (fieldAffinePointOne F U) ∧
        y ∈ conjugatesOf (fieldAffinePointOne F U) ∧
        x * y = fieldAffinePointOne F U ^ 2 := Iff.rfl

theorem fieldAffineSquarePairs_eq_image (hm : m ≠ 0) :
    fieldAffineSquarePairs F (normOneSubgroup F m)
      = (fun a : F => ((inl (Multiplicative.ofAdd a) : fieldAffineGroup F (normOneSubgroup F m)),
          inl (Multiplicative.ofAdd (2 - a)))) '' normOneShiftSet F m := by
  ext ⟨x, y⟩
  rw [mem_fieldAffineSquarePairs]
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨u, hu, rfl⟩ := mem_conjugatesOf_fieldAffinePointOne.1 h1
    obtain ⟨v, hv, rfl⟩ := mem_conjugatesOf_fieldAffinePointOne.1 h2
    rw [inl_ofAdd_mul_inl_ofAdd, fieldAffinePointOne_sq] at h3
    have hsum : (u : F) + (v : F) = 2 := inl_ofAdd_injective h3
    have hv' : ((v : F)) = 2 - (u : F) := by rw [← hsum]; ring
    refine ⟨(u : F), mem_normOneShiftSet.2 ⟨pow_eq_one_of_mem_normOneSubgroup hu, ?_⟩, ?_⟩
    · rw [← hv']; exact pow_eq_one_of_mem_normOneSubgroup hv
    · rw [hv']
  · rintro ⟨a, ha, hP⟩
    obtain ⟨ha1, ha2⟩ := mem_normOneShiftSet.1 ha
    have ha0 : a ≠ 0 := by rintro rfl; simp [hm] at ha1
    have hb0 : 2 - a ≠ 0 := by intro h; rw [h] at ha2; simp [hm] at ha2
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hP
    refine ⟨mem_conjugatesOf_fieldAffinePointOne.2 ⟨Units.mk0 a ha0, ?_, rfl⟩,
      mem_conjugatesOf_fieldAffinePointOne.2 ⟨Units.mk0 (2 - a) hb0, ?_, rfl⟩, ?_⟩
    · exact mem_normOneSubgroup.2 (Units.ext (by simpa using ha1))
    · exact mem_normOneSubgroup.2 (Units.ext (by simpa using ha2))
    · rw [inl_ofAdd_mul_inl_ofAdd, fieldAffinePointOne_sq]
      congr 2
      ring

theorem ncard_fieldAffineSquarePairs (hm : m ≠ 0) :
    (fieldAffineSquarePairs F (normOneSubgroup F m)).ncard = (normOneShiftSet F m).ncard := by
  rw [fieldAffineSquarePairs_eq_image hm]
  exact Set.ncard_image_of_injective _
    fun _ _ hab => inl_ofAdd_injective (congrArg Prod.fst hab)

theorem classStructureConstant_fieldAffinePointOne [Fintype (fieldAffineGroup F U)]
    [DecidableEq (fieldAffineGroup F U)] :
    classStructureConstant (ConjClasses.mk (fieldAffinePointOne F U))
        (ConjClasses.mk (fieldAffinePointOne F U))
        (ConjClasses.mk (fieldAffinePointOne F U ^ 2))
      = (fieldAffineSquarePairs F U).ncard := by
  rw [classStructureConstant_eq_card, ← Set.ncard_coe_finset]
  congr 1
  ext ⟨x, y⟩
  simp only [Finset.mem_coe, mem_classProdPairs, mem_fieldAffineSquarePairs, conjugatesOf,
    Set.mem_ofPred_eq]
  rw [ConjClasses.mk_eq_mk_iff_isConj, ConjClasses.mk_eq_mk_iff_isConj]
  exact ⟨fun h => ⟨h.1.symm, h.2.1.symm, h.2.2⟩, fun h => ⟨h.1.symm, h.2.1.symm, h.2.2⟩⟩

section Config

theorem classCoefficient_fieldAffinePointOne_of_config
    [Fintype (fieldAffineGroup F (normOneSubgroup F m))]
    [DecidableEq (fieldAffineGroup F (normOneSubgroup F m))] (hp : p.Prime) (_hq : q.Prime)
    (_hqp : q < p) (hFcard : Nat.card F = p ^ q) (hm : m = (p ^ q - 1) / (p - 1))
    (_hcop : Nat.Coprime m (p - 1)) :
    classStructureConstant (ConjClasses.mk (fieldAffinePointOne F (normOneSubgroup F m)))
          (ConjClasses.mk (fieldAffinePointOne F (normOneSubgroup F m)))
          (ConjClasses.mk (fieldAffinePointOne F (normOneSubgroup F m) ^ 2))
        = (fieldAffineSquarePairs F (normOneSubgroup F m)).ncard ∧
      (fieldAffineSquarePairs F (normOneSubgroup F m)).ncard = (normOneShiftSet F m).ncard ∧
      (conjugatesOf (fieldAffinePointOne F (normOneSubgroup F m))).ncard = m := by
  have hm0 : m ≠ 0 := by
    rw [hm, ← Nat.geomSum_eq hp.two_le]
    exact (geomSum_pos_of_natCard_eq_prime_pow (F := F) hp hFcard).ne'
  refine ⟨classStructureConstant_fieldAffinePointOne, ncard_fieldAffineSquarePairs hm0, ?_⟩
  rw [ncard_conjugatesOf_fieldAffinePointOne, natCard_normOneSubgroup hp hFcard hm]

end Config

end

end CFSG.FeitThompson
