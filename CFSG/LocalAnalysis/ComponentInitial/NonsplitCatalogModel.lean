module

public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalSignedPerms
public import CFSG.LinearAlgebra.AnisotropicBinaryPlane

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.NonsplitCatalog

open QuadraticMap CFSG.ClassicalGroups.Orthogonal OrthogonalTail NormTail
open CFSG.LieType.Universal.Spin

section NormField

variable {K : Type} [Field K] {ε : K}

variable (K ε) in
@[expose] def starAlgEquiv : QuadraticAlgebra K 1 ε ≃ₐ[K] QuadraticAlgebra K 1 ε :=
  AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by
    ext <;> simp

theorem starAlgEquiv_apply (z : QuadraticAlgebra K 1 ε) : starAlgEquiv K ε z = star z :=
  rfl

theorem finrank_normTailData : Module.finrank K (QuadraticAlgebra K 1 ε) = 2 :=
  QuadraticAlgebra.finrank_eq_two 1 ε

variable [Fact (∀ r : K, r ^ 2 ≠ 1 + ε * r)]

theorem ne_zero_of_fact : ε ≠ 0 := fun h =>
  (Fact.out : ∀ r : K, r ^ 2 ≠ 1 + ε * r) 1 (by rw [h]; ring)

variable (K ε) in
@[expose] def normTailData : NormTailData K (QuadraticAlgebra K 1 ε) where
  bar := starAlgEquiv K ε
  bar_bar z := star_star z
  exists_eq_of_bar_eq z hz := by
    refine ⟨z.re, ?_⟩
    have him : z.im = 0 := by
      have h := congrArg QuadraticAlgebra.re hz
      rw [starAlgEquiv_apply, QuadraticAlgebra.re_star, add_eq_left] at h
      exact (mul_eq_zero.1 h).resolve_left ne_zero_of_fact
    rw [QuadraticAlgebra.algebraMap_eq]
    ext
    · rfl
    · exact him.symm

theorem normForm_normTailData [CharP K 2] (z : QuadraticAlgebra K 1 ε) :
    normForm (normTailData K ε) z = z.re ^ 2 + ε * z.re * z.im + z.im ^ 2 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hz : z * (normTailData K ε).bar z =
      algebraMap K _ (z.re ^ 2 + ε * z.re * z.im + z.im ^ 2) := by
    change z * star z = _
    rw [QuadraticAlgebra.algebraMap_eq]
    ext
    · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
      linear_combination (-z.im ^ 2) * h2
    · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
      ring
  rw [normForm_apply, hz, retr_algebraMap]

end NormField

section Isometry

variable {K : Type} [Field K] [CharP K 2] {ε : K} [Fact (∀ r : K, r ^ 2 ≠ 1 + ε * r)]

variable (ε) in
@[expose] def tailEquiv {a : K} (ha : a ≠ 0) : QuadraticAlgebra K 1 ε ≃ₗ[K] (Fin 2 → K) where
  toFun z := ![z.re, a⁻¹ * z.im]
  invFun v := ⟨v 0, a * v 1⟩
  map_add' z w := by
    ext i
    fin_cases i <;> simp [mul_add]
  map_smul' t z := by
    ext i
    fin_cases i <;> simp [mul_left_comm]
  left_inv z := by
    ext
    · rfl
    · simp [mul_inv_cancel_left₀ ha]
  right_inv v := by
    ext i
    fin_cases i
    · rfl
    · simp [inv_mul_cancel_left₀ ha]

@[expose] def tailIsometry {a b c : K} (ha : a ≠ 0) (hc : a ^ 2 = c) (hε : ε = b / a) :
    (normForm (normTailData K ε)).IsometryEquiv (minusTailForm K b c) where
  toLinearEquiv := tailEquiv ε ha
  map_app' z := by
    have hb : b = ε * a := by rw [hε]; field_simp
    change minusTailForm K b c ![z.re, a⁻¹ * z.im] = _
    rw [minusTailForm_apply, normForm_normTailData, hb, ← hc]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp

end Isometry

theorem anisotropic_of_irreducible {K : Type} [Field K] [CharP K 2] {a b c : K} (ha : a ≠ 0)
    (hc : a ^ 2 = c) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∀ x y : K, x ^ 2 + b / a * x * y + y ^ 2 = 0 → x = 0 ∧ y = 0 := by
  intro x y hxy
  by_cases hy : y = 0
  · subst hy
    refine ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by linear_combination hxy), rfl⟩
  · exfalso
    have h0 : a * x ^ 2 + b * x * y + a * y ^ 2 = 0 := by
      rw [show a * x ^ 2 + b * x * y + a * y ^ 2 = a * (x ^ 2 + b / a * x * y + y ^ 2) by
        field_simp, hxy, mul_zero]
    refine hirr (a * x / y) ?_
    rw [show (a * x / y) ^ 2 + b * (a * x / y) + c =
        a / y ^ 2 * (a * x ^ 2 + b * x * y + a * y ^ 2) by rw [← hc]; field_simp, h0,
      mul_zero]

theorem exists_normTail_of_lieModel {J : Type} [Group J] {n f : ℕ}
    (hJ : CFSG.Blueprint.LieModel J .POmegaMinus n 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧ 4 ≤ n ∧
      ∃ (F : Type) (_ : Field F) (_ : Algebra K F) (T : NormTailData K F),
        Module.finrank K F = 2 ∧ Nonempty (J ≃* G0 T (n - 1)) := by
  rcases hJ with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨⟨-, -, hn⟩, K, hK, hfin, hcard, b, c, hirr, ⟨e⟩⟩ := hc
    have hn' : 4 ≤ n := hn
    have hf : 1 ≤ f := by
      by_contra hf0
      have h1 : Nat.card K = 1 := by rw [hcard, show f = 0 by omega, pow_zero]
      have := Finite.one_lt_card (α := K)
      omega
    have hchar : CharP K 2 :=
      finite_field_prime_power_characteristic (K := K) Nat.prime_two hf hcard
    have hc0 : c ≠ 0 := fun h => hirr 0 (by rw [h]; ring)
    obtain ⟨a, ha⟩ : ∃ a : K, a ^ 2 = c := by
      obtain ⟨a, ha⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
      exact ⟨a, by rw [ha, _root_.sq]⟩
    have ha0 : a ≠ 0 := fun h => hc0 (by rw [← ha, h]; ring)
    have hb0 : b ≠ 0 := fun h => hirr a (by
      rw [h, ha]
      linear_combination c * (CharTwo.two_eq_zero (R := K)))
    have hQ := anisotropic_of_irreducible ha0 ha hirr
    have : Fact (∀ r : K, r ^ 2 ≠ 1 + b / a * r) :=
      ⟨CFSG.LinearAlgebra.sq_ne_one_add_mul_of_anisotropic hQ⟩
    set T := normTailData K (b / a)
    have hE := commutator_orthogonalGroup_quadMinus hn' hirr
    set ψ : (quadTail (n - 1) (normForm T)).IsometryEquiv (quadMinus n K b c) :=
      (QuadraticMap.IsometryEquiv.prod (QuadraticMap.IsometryEquiv.refl (quadPlus (n - 1) K))
        (tailIsometry ha0 ha rfl)).trans (minusTailIsometry n K b c)
    exact ⟨K, hK, hfin, hchar, hcard, hn', QuadraticAlgebra K 1 (b / a), inferInstance,
      inferInstance, T, finrank_normTailData, ⟨e.trans ((tailProjEquiv ψ (coe_quadMinus n K b c)
        hE).trans ((QuotientGroup.quotientMulEquivOfEq
          (NonsplitOrthogonalCover.elemScalars_quadTail_eq_bot (by omega))).trans
            QuotientGroup.quotientBot))⟩⟩
  all_goals exact absurd ht (by decide)

end CFSG.LocalAnalysis.ComponentInitial.NonsplitCatalog
