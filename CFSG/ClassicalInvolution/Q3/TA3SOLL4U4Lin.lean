module

public import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4LinN

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.L4U4

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.CatFactsL4U4 CFSG.ComponentClassification.CatFactsL4U4.TBlocks
open CFSG.ComponentClassification.CatFactsL4U4.HBlocks
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem eq_one_of_proj_conj_bdSL {P : GL (Fin 4) K} {x : SL(2, K) × SL(2, K)}
    (hx : proj 4 K (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 K P
      (InvClassL.bdSL x)) = 1)
    (h1 : x.1 = 1 ∨ x.2 = 1) : x = 1 := by
  set c := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 K P
  have hz : c (InvClassL.bdSL x) ∈ Subgroup.center SL(4, K) := by
    rw [← scalars_eq_center]
    exact proj_eq_one_iff.mp hx
  have hz' : InvClassL.bdSL x ∈ scalars 4 K := by
    rw [scalars_eq_center, Subgroup.mem_center_iff]
    intro y
    apply c.injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp hz (c y)
  obtain ⟨ζ, -, hζ⟩ := mem_scalars.1 hz'
  rw [InvClassL.coe_bdSL] at hζ
  have he : ∀ i j, bd (x.1 : Matrix (Fin 2) (Fin 2) K) (x.2 : Matrix (Fin 2) (Fin 2) K) i j =
      if i = j then (ζ : K) else 0 := fun i j => by rw [hζ, scalar_apply, diagonal_apply]
  have e00 := he 0 0
  have e01 := he 0 1
  have e10 := he 1 0
  have e11 := he 1 1
  have f00 := he 2 2
  have f01 := he 2 3
  have f10 := he 3 2
  have f11 := he 3 3
  simp [bd] at e00 e01 e10 e11 f00 f01 f10 f11
  have hζ1 : (ζ : K) = 1 := by
    rcases h1 with h1 | h1
    · rw [h1] at e00
      simpa using e00.symm
    · rw [h1] at f00
      simpa using f00.symm
  refine Prod.ext (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)
    (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)
  · fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11, hζ1]
  · fin_cases i <;> fin_cases j <;> simp [f00, f01, f10, f11, hζ1]

omit [Finite K] in
theorem conj_comm {n : Type*} [Fintype n] [DecidableEq n] {P : GL n K} {M N : Matrix n n K}
    (h : M * N = N * M) :
    (P : Matrix n n K) * M * ((P⁻¹ : GL n K) : Matrix n n K) *
        ((P : Matrix n n K) * N * ((P⁻¹ : GL n K) : Matrix n n K)) =
      (P : Matrix n n K) * N * ((P⁻¹ : GL n K) : Matrix n n K) *
        ((P : Matrix n n K) * M * ((P⁻¹ : GL n K) : Matrix n n K)) := by
  have hPP : ((P⁻¹ : GL n K) : Matrix n n K) * (P : Matrix n n K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc _ = (P : Matrix n n K) * (M * N) * ((P⁻¹ : GL n K) : Matrix n n K) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc _ (P : Matrix n n K), hPP, Matrix.one_mul]
    _ = (P : Matrix n n K) * (N * M) * ((P⁻¹ : GL n K) : Matrix n n K) := by rw [h]
    _ = _ := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc _ (P : Matrix n n K), hPP, Matrix.one_mul]

omit [Finite K] in
theorem twoSL2Shape_of_frame {g : SL(4, K)} {l : K} (hl0 : l ≠ 0) (P : GL (Fin 4) K)
    (hP : (l⁻¹ • (g : Matrix (Fin 4) (Fin 4) K)) * (P : Matrix (Fin 4) (Fin 4) K) =
      (P : Matrix (Fin 4) (Fin 4) K) * X1 1) :
    TwoSL2Shape (projectiveSL 4 K) (proj 4 K g) K := by
  set c := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 K P
  set φ₁ := (proj 4 K).comp (c.toMonoidHom.comp
    (InvClassL.bdSL.comp (MonoidHom.inl _ _))) with hφ₁
  set φ₂ := (proj 4 K).comp (c.toMonoidHom.comp
    (InvClassL.bdSL.comp (MonoidHom.inr _ _))) with hφ₂
  have hi₁ : Function.Injective φ₁ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have := eq_one_of_proj_conj_bdSL (x := (a, 1)) ha (Or.inr rfl)
    exact congrArg Prod.fst this
  have hi₂ : Function.Injective φ₂ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have := eq_one_of_proj_conj_bdSL (x := (1, b)) hb (Or.inl rfl)
    exact congrArg Prod.snd this
  have hg : (g : Matrix (Fin 4) (Fin 4) K) = l • ((P : Matrix (Fin 4) (Fin 4) K) * X1 1 *
      ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by
    rw [← hP, Matrix.smul_mul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hl0, one_smul,
      Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have hC : ∀ x : SL(2, K) × SL(2, K), proj 4 K (c (InvClassL.bdSL x)) ∈
      Subgroup.centralizer ({proj 4 K g} : Set (projectiveSL 4 K)) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_slConjugation,
      hg, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    exact conj_comm (InvClassL.bdSL_comm x)
  refine ⟨φ₁.range, φ₂.range, ?_, ?_, ?_, ⟨(MonoidHom.ofInjective hi₁).symm⟩,
    ⟨(MonoidHom.ofInjective hi₂).symm⟩⟩
  · rintro _ ⟨a, rfl⟩
    exact hC (a, 1)
  · rintro _ ⟨b, rfl⟩
    exact hC (1, b)
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    simp only [hφ₁, hφ₂, MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
      MulEquiv.coe_toMonoidHom, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]

theorem false_of_det_neg_one (hK : ringChar K ≠ 2) (h8 : Nat.card K % 8 ≠ 1) {g : SL(4, K)}
    {l : K} (hl0 : l ≠ 0) (hdet : (l⁻¹ • (g : Matrix (Fin 4) (Fin 4) K)).det = -1) : False := by
  have := Fintype.ofFinite K
  rw [det_smul, g.2, mul_one, Fintype.card_fin] at hdet
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf l⁻¹ = 2 ^ (2 + 1) := by
    refine orderOf_eq_prime_pow ?_ ?_
    · rw [show (2 : ℕ) ^ 2 = 4 by norm_num, hdet]
      intro h1
      exact h2 (by linear_combination -h1)
    · rw [show (2 : ℕ) ^ (2 + 1) = 4 * 2 by norm_num, pow_mul, hdet]
      norm_num
  have hq : l⁻¹ ^ (Fintype.card K - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one _ (inv_ne_zero hl0)
  have hdvd : 2 ^ (2 + 1) ∣ Fintype.card K - 1 := hord ▸ orderOf_dvd_of_pow_eq_one hq
  have hpos : 0 < Fintype.card K := Fintype.card_pos
  have h8' : Fintype.card K % 8 ≠ 1 := by rwa [← Nat.card_eq_fintype_card]
  norm_num at hdvd
  omega

theorem lin_shape (hK : ringChar K ≠ 2) (h8 : Nat.card K % 8 ≠ 1) {z : projectiveSL 4 K}
    (hz : orderOf z = 2) :
    TwoSL2Shape (projectiveSL 4 K) z K ∨ NormalSimpleShape (projectiveSL 4 K) z := by
  obtain ⟨g, rfl⟩ := proj_surjective 4 K z
  have hg2 : proj 4 K (g * g) = 1 := by
    rw [map_mul, ← sq, ← hz, pow_orderOf_eq_one]
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 hg2)
  have hX : (g : Matrix (Fin 4) (Fin 4) K) * g = (c : K) • 1 := by
    have hc' : (g : Matrix (Fin 4) (Fin 4) K) * g = scalar (Fin 4) (c : K) := hc
    rw [hc', scalar_apply, smul_one_eq_diagonal]
  have hns : ∀ a : K, (g : Matrix (Fin 4) (Fin 4) K) ≠ a • 1 := by
    intro a ha
    have hdet : a ^ 4 = 1 := by
      have h1 := g.2
      rw [ha, det_smul, det_one, mul_one, Fintype.card_fin] at h1
      exact h1
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at hdet
    have h1 : proj 4 K g = 1 := proj_eq_one_iff.2 ⟨Units.mk0 a ha0,
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hdet, Units.val_one]), by
        rw [ha, Units.val_mk0, scalar_apply, smul_one_eq_diagonal]⟩
    rw [h1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  rcases InvClassL.classify_inv hK hX c.ne_zero hns with
    ⟨l, hl0, -, -, P, hP⟩ | ⟨l, hl0, -, hdet, -⟩ | ⟨hsq, -⟩
  · exact Or.inl (twoSL2Shape_of_frame hl0 P hP)
  · exact (false_of_det_neg_one hK h8 hl0 hdet).elim
  · exact Or.inr (normalSimpleShape_of_nonsquare hK c.ne_zero hsq hX)

end CFSG.ClassicalInvolution.Q3.TA3.L4U4
