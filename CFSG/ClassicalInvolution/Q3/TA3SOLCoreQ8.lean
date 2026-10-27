module

public import CFSG.ClassicalInvolution.Q3.Q3TLTDatum
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieModelSL2
public import CFSG.ClassicalInvolution.Models.LinearPairs.RootSL2

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution QuaternionGroup
open CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal
open CFSG.ComponentClassification.RankTwoOddLie
open scoped MatrixGroups

theorem q8_central : ∀ x : QuaternionGroup 2, (∀ y, x * y = y * x) → x = 1 ∨ x = a 2 := by
  decide

theorem q8_a_one_sq : (a 1 : QuaternionGroup 2) ^ 2 = a 2 := by decide

theorem q8Hom_a_one {X : Type} [Group X] {p q : X} (h : IsQ8Pair p q) : q8Hom h (a 1) = p := by
  show zmod4Pow p 1 = p
  unfold zmod4Pow
  rw [show (1 : ZMod 4).val = 1 from rfl, pow_one]

theorem q8Hom_mem {X : Type} [Group X] {p q : X} (h : IsQ8Pair p q) {K : Subgroup X}
    (hp : p ∈ K) (hq : q ∈ K) (x : QuaternionGroup 2) : q8Hom h x ∈ K := by
  cases x with
  | a i => exact K.pow_mem hp _
  | xa i => exact K.mul_mem hq (K.pow_mem hp _)

variable {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R} {t : X}

theorem datum_exists_q8 (hD : TightDatum R S t) :
    ∃ φ : QuaternionGroup 2 →* X, Function.Injective φ ∧ (∀ x, φ x ∈ R) ∧
      φ (a 1) ^ 2 = t := by
  obtain ⟨r, hr, ⟨eS⟩⟩ := hD.quat
  set S' : Subgroup X := (S : Subgroup R).map R.subtype with hS'
  have hQ : CFSG.ComponentClassification.AschbacherTheorem3.IsQuaternionTwoGroup S' :=
    ⟨r, hr, ⟨(Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype
      R.subtype_injective).symm.trans eS⟩⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_q8Pair hQ
  have hS'R : S' ≤ R := Subgroup.map_subtype_le _
  refine ⟨q8Hom hpq, q8Hom_injective hpq, fun x => hS'R (q8Hom_mem hpq hp hq x), ?_⟩
  rw [q8Hom_a_one]
  refine hD.eq_of_orderOf_eq_two (R.pow_mem (hS'R hp) 2) (orderOf_eq_prime ?_ hpq.2.2.2)
  rw [← pow_mul]
  exact hpq.1

theorem isQ8Pair_qI_qJ {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {a b : F}
    (hab : a ^ 2 + b ^ 2 = -1) : IsQ8Pair (qI : SL(2, F)) (qJ hab) := by
  refine ⟨qI_pow_four, (qJ_sq hab).trans qI_sq.symm, ?_, ?_⟩
  · rw [qJ_mul_qI hab, mul_assoc, mul_inv_cancel, mul_one]
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, qI_pow_four]
  · rw [qI_sq]
    intro h
    have h1 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h1
    exact h2 (by linear_combination -h1)

omit [Finite X] in
theorem exists_q8_of_mulEquiv_sl2 {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F))
    (H : Subgroup X) (e : H ≃* SL(2, F)) :
    ∃ φ : QuaternionGroup 2 →* X, Function.Injective φ ∧ (∀ x, φ x ∈ H) ∧
      φ (a 1) ^ 2 = ((e.symm (-1) : H) : X) := by
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hF
  obtain ⟨a', b', hab⟩ := exists_sq_add_sq_eq_neg_one (F := F)
  have hpq := isQ8Pair_qI_qJ h2 hab
  refine ⟨(H.subtype.comp e.symm.toMonoidHom).comp (q8Hom hpq),
    H.subtype_injective.comp (e.symm.injective.comp (q8Hom_injective hpq)),
    fun x => ((e.symm (q8Hom hpq x)) : H).2, ?_⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    MulEquiv.coe_toMonoidHom, q8Hom_a_one]
  rw [← Subgroup.coe_pow, ← map_pow, qI_sq]

end CFSG.ClassicalInvolution.Q3.TA3
