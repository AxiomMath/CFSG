module

public import CFSG.FeitThompson.Representations.ClassSumsIntegerStructureConstants
public import CFSG.FeitThompson.Representations.CentralElementsSeparatedIrreducibles
public import CFSG.FeitThompson.Representations.CharacterMultiplicitiesIrreducibility
import CFSG.FeitThompson.Representations.CentralCharacterClassSumIntegral
import CFSG.FeitThompson.Representations.CentralPrimitiveIdempotentsGroupAlgebra
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open ComplexConjugate

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

noncomputable def conjPairsProdEq (x y z : G) : Finset (G × G) :=
  {p ∈ conjClassFinset x ×ˢ conjClassFinset y | p.1 * p.2 = z}

@[simp]
theorem mem_conjPairsProdEq {x y z : G} {p : G × G} :
    p ∈ conjPairsProdEq x y z ↔ IsConj x p.1 ∧ IsConj y p.2 ∧ p.1 * p.2 = z := by
  simp [conjPairsProdEq, and_assoc]

theorem coe_conjPairsProdEq (x y z : G) :
    (conjPairsProdEq x y z : Set (G × G))
      = {p : G × G | IsConj x p.1 ∧ IsConj y p.2 ∧ p.1 * p.2 = z} := by
  ext p
  simpa using mem_conjPairsProdEq

theorem conjPairsProdEq_eq_classProdPairs (x y z : G) :
    conjPairsProdEq x y z = classProdPairs (ConjClasses.mk x) (ConjClasses.mk y) z := by
  ext p
  rw [mem_conjPairsProdEq, mem_classProdPairs, ConjClasses.mk_eq_mk_iff_isConj,
    ConjClasses.mk_eq_mk_iff_isConj]
  exact and_congr isConj_comm (and_congr isConj_comm Iff.rfl)

theorem card_conjPairsProdEq_eq_of_isConj (x y : G) {z z' : G} (h : IsConj z z') :
    (conjPairsProdEq x y z).card = (conjPairsProdEq x y z').card := by
  rw [conjPairsProdEq_eq_classProdPairs, conjPairsProdEq_eq_classProdPairs,
    card_classProdPairs_eq_of_isConj _ _ h]

omit [Fintype G] [DecidableEq G] in
theorem irrChar_one_ne_zero {χ : G → ℂ} (hχ : χ ∈ irrChar ℂ G) : χ 1 ≠ 0 := by
  rw [← character_irrRep hχ]
  exact character_one_ne_zero (irrRep hχ).ρ

omit [Fintype G] [DecidableEq G] in
theorem sum_irrChar_eq_sum_irrFinset [Finite G] [Fintype (irrChar ℂ G)] (f : (G → ℂ) → ℂ) :
    ∑ χ : irrChar ℂ G, f (χ : G → ℂ) = ∑ χ ∈ irrFinset G, f χ := by
  rw [Finset.sum_set_coe (s := irrChar ℂ G)]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext χ
  rw [Set.mem_toFinset, mem_irrFinset, Irr_eq_irrChar]

theorem centralScalar_centerClassSum {χ : G → ℂ} (hχ : χ ∈ irrChar ℂ G) (x : G) :
    centralScalar hχ (centerClassSum ℂ (ConjClasses.mk x))
      = ((conjClassFinset x).card : ℂ) * χ x / χ 1 := by
  rw [← centralCharacter_eq_centralScalar (irrRep hχ).ρ hχ (character_irrRep hχ),
    centerClassSum_mk, Representation.centralCharacter_conjClassSum, character_irrRep]

theorem card_conjPairsProdEq (x y z : G) :
    ((conjPairsProdEq x y z).card : ℂ)
      = ((conjClassFinset x).card * (conjClassFinset y).card / (Nat.card G : ℂ)) *
        ∑ χ ∈ irrFinset G, χ x * χ y * conj (χ z) / χ 1 := by
  have : Fintype (irrChar ℂ G) := Fintype.ofFinite _
  rw [conjPairsProdEq_eq_classProdPairs,
    ← sum_irrChar_eq_sum_irrFinset (fun χ : G → ℂ => χ x * χ y * conj (χ z) / χ 1)]
  set K := ConjClasses.mk x
  set L := ConjClasses.mk y
  set w : Subalgebra.center ℂ (MonoidAlgebra ℂ G) := centerClassSum ℂ K * centerClassSum ℂ L
    with hw
  have hcoe : (w : MonoidAlgebra ℂ G) = classSum ℂ K * classSum ℂ L := by
    rw [hw]; push_cast [coe_centerClassSum]; rfl
  have h1 : (w : MonoidAlgebra ℂ G).coeff z = ((classProdPairs K L z).card : ℂ) := by
    rw [hcoe, coeff_classSum_mul_classSum]
  rw [coe_eq_sum_centralScalar_smul_centralIdempotent w] at h1
  rw [← h1, MonoidAlgebra.coeff_sum]
  simp only [Finsupp.finsetSum_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun χ _ => ?_
  have hne : (χ : G → ℂ) 1 ≠ 0 := irrChar_one_ne_zero χ.2
  rw [MonoidAlgebra.coeff_smul_apply, coeff_centralIdempotent, hw, map_mul,
    centralScalar_centerClassSum, centralScalar_centerClassSum, smul_eq_mul]
  field_simp

theorem ncard_setOf_isConj_isConj_mul_eq (x y z : G) :
    (({p : G × G | IsConj x p.1 ∧ IsConj y p.2 ∧ p.1 * p.2 = z}.ncard : ℕ) : ℂ)
      = ((conjClassFinset x).card * (conjClassFinset y).card / (Nat.card G : ℂ)) *
        ∑ χ ∈ irrFinset G, χ x * χ y * conj (χ z) / χ 1 := by
  rw [← coe_conjPairsProdEq, Set.ncard_coe_finset, card_conjPairsProdEq]

end CFSG.FeitThompson
