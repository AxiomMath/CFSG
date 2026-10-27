module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open Matrix
open scoped MatrixGroups

section Conj

variable {R : Type*} [CommRing R]

@[expose] def conjSL (g : GL (Fin 2) R) : SL(2, R) →* SL(2, R) where
  toFun b := ⟨(g : Matrix (Fin 2) (Fin 2) R) * (b : Matrix (Fin 2) (Fin 2) R) *
      ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R), by
    rw [Matrix.det_mul, Matrix.det_mul, b.det_coe, mul_one, ← Matrix.det_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.det_one]⟩
  map_one' := by
    apply Subtype.ext
    show (g : Matrix (Fin 2) (Fin 2) R) * (1 : Matrix (Fin 2) (Fin 2) R) *
      ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = 1
    rw [Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  map_mul' a b := by
    apply Subtype.ext
    show (g : Matrix (Fin 2) (Fin 2) R) * ((a : Matrix (Fin 2) (Fin 2) R) *
          (b : Matrix (Fin 2) (Fin 2) R)) * ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      ((g : Matrix (Fin 2) (Fin 2) R) * (a : Matrix (Fin 2) (Fin 2) R) *
          ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)) *
        ((g : Matrix (Fin 2) (Fin 2) R) * (b : Matrix (Fin 2) (Fin 2) R) *
          ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R))
    have hGG : ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) *
        (g : Matrix (Fin 2) (Fin 2) R) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (g : Matrix (Fin 2) (Fin 2) R) * ((a : Matrix (Fin 2) (Fin 2) R) *
          (b : Matrix (Fin 2) (Fin 2) R)) * ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
        = (g : Matrix (Fin 2) (Fin 2) R) * (a : Matrix (Fin 2) (Fin 2) R) * 1 *
            (b : Matrix (Fin 2) (Fin 2) R) *
          ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) := by
          simp [Matrix.mul_assoc]
      _ = _ := by rw [← hGG]; simp only [Matrix.mul_assoc]

theorem coe_conjSL (g : GL (Fin 2) R) (b : SL(2, R)) :
    ((conjSL g b : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) =
      (g : Matrix (Fin 2) (Fin 2) R) * (b : Matrix (Fin 2) (Fin 2) R) *
        ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) := rfl

theorem conjSL_one : conjSL (1 : GL (Fin 2) R) = MonoidHom.id _ := by
  ext b : 2
  simp [coe_conjSL]

theorem conjSL_mul (g h : GL (Fin 2) R) : conjSL (g * h) = (conjSL g).comp (conjSL h) := by
  ext b : 2
  simp [coe_conjSL, Matrix.mul_assoc]

@[expose] def conjAut : GL (Fin 2) R →* MulAut SL(2, R) where
  toFun g := MonoidHom.toMulEquiv (conjSL g) (conjSL g⁻¹)
    (by rw [← conjSL_mul, inv_mul_cancel, conjSL_one])
    (by rw [← conjSL_mul, mul_inv_cancel, conjSL_one])
  map_one' := by
    ext b : 2
    simp [conjSL_one]
  map_mul' g h := by
    ext b : 2
    simp [conjSL_mul]

theorem conjAut_apply (g : GL (Fin 2) R) (b : SL(2, R)) : conjAut g b = conjSL g b := rfl

end Conj

section Gen

@[expose] def autGenS : SL(2, ZMod 3) := ⟨!![0, -1; 1, 0], by decide⟩

@[expose] def autGenT : SL(2, ZMod 3) := ⟨!![1, 1; 0, 1], by decide⟩

theorem autGenS_pow_four : autGenS ^ 4 = 1 := by decide +kernel

theorem autGenS_rel : autGenS ^ 2 = (autGenS * autGenT) ^ 3 := by decide +kernel

theorem autGenT_pow_three : autGenT ^ 3 = 1 := by decide +kernel

theorem autGenS_sq_ne_one : autGenS ^ 2 ≠ 1 := by decide +kernel

private def evalWord : List Bool → SL(2, ZMod 3)
  | [] => 1
  | b :: w => (if b then autGenT else autGenS) * evalWord w

private def allWords : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => [] :: ((allWords n).flatMap fun w => [false :: w, true :: w])

private theorem evalWord_mem (w : List Bool) :
    evalWord w ∈ Subgroup.closure ({autGenS, autGenT} : Set (SL(2, ZMod 3))) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons b w ih =>
    refine Subgroup.mul_mem _ ?_ ih
    cases b
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)

private theorem cover_aux : ∀ x : SL(2, ZMod 3), ∃ w ∈ allWords 9, evalWord w = x := by
  decide +kernel

theorem autGen_closure_eq_top :
    Subgroup.closure ({autGenS, autGenT} : Set (SL(2, ZMod 3))) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨w, -, rfl⟩ := cover_aux x
  exact evalWord_mem w

private theorem pair_conj_aux : ∀ h₁ h₂ : SL(2, ZMod 3), h₁ ^ 4 = 1 → h₁ ^ 2 = (h₁ * h₂) ^ 3 →
    h₂ ^ 3 = 1 → h₁ ^ 2 ≠ 1 →
      ∃ (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) (u : ZMod 3), g.det * u = 1 ∧
        g * (autGenS : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
          (h₁ : Matrix (Fin 2) (Fin 2) (ZMod 3)) * g ∧
        g * (autGenT : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
          (h₂ : Matrix (Fin 2) (Fin 2) (ZMod 3)) * g := by
  decide +kernel

end Gen

section Main

private theorem eq_conj_of_mul_eq {R : Type*} [CommRing R] (G : GL (Fin 2) R)
    {x y : Matrix (Fin 2) (Fin 2) R}
    (h : (G : Matrix (Fin 2) (Fin 2) R) * x = y * (G : Matrix (Fin 2) (Fin 2) R)) :
    y = (G : Matrix (Fin 2) (Fin 2) R) * x * ((G⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) := by
  rw [h, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem sl2Three_aut_eq_conj (α : MulAut SL(2, ZMod 3)) :
    ∃ g : GL (Fin 2) (ZMod 3), ∀ b : SL(2, ZMod 3),
      ((α b : SL(2, ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
        (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
          ((g⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
  have e1 : (α autGenS) ^ 4 = 1 := by rw [← map_pow, autGenS_pow_four, map_one]
  have e2 : (α autGenS) ^ 2 = (α autGenS * α autGenT) ^ 3 := by
    rw [← map_pow, ← map_mul, ← map_pow, autGenS_rel]
  have e3 : (α autGenT) ^ 3 = 1 := by rw [← map_pow, autGenT_pow_three, map_one]
  have e4 : (α autGenS) ^ 2 ≠ 1 := by
    intro h
    rw [← map_pow, ← map_one α] at h
    exact autGenS_sq_ne_one (α.injective h)
  obtain ⟨g, u, hdet, hS, hT⟩ := pair_conj_aux _ _ e1 e2 e3 e4
  let G : GL (Fin 2) (ZMod 3) := Matrix.GeneralLinearGroup.mk'' g (IsUnit.of_mul_eq_one u hdet)
  have hG : (G : Matrix (Fin 2) (Fin 2) (ZMod 3)) = g := rfl
  refine ⟨G, fun b => ?_⟩
  have key : (α : SL(2, ZMod 3) →* SL(2, ZMod 3)) = conjSL G := by
    apply MonoidHom.eq_of_eqOn_dense autGen_closure_eq_top
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Subtype.ext (eq_conj_of_mul_eq G (by rw [hG]; exact hS))
    · exact Subtype.ext (eq_conj_of_mul_eq G (by rw [hG]; exact hT))
  have := congrArg (fun f : SL(2, ZMod 3) →* SL(2, ZMod 3) =>
    ((f b : SL(2, ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))) key
  simpa [coe_conjSL] using this

theorem conjAut3_surjective :
    Function.Surjective (conjAut : GL (Fin 2) (ZMod 3) →* MulAut SL(2, ZMod 3)) := by
  intro α
  obtain ⟨g, hg⟩ := sl2Three_aut_eq_conj α
  refine ⟨g, ?_⟩
  ext b : 1
  exact Subtype.ext (by rw [conjAut_apply, coe_conjSL, hg b])

end Main

section Ker

private theorem scalar_aux : ∀ g : Matrix (Fin 2) (Fin 2) (ZMod 3),
    (∃ u : ZMod 3, g.det * u = 1) →
    g * (autGenS : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      (autGenS : Matrix (Fin 2) (Fin 2) (ZMod 3)) * g →
    g * (autGenT : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      (autGenT : Matrix (Fin 2) (Fin 2) (ZMod 3)) * g → g = 1 ∨ g = -1 := by
  decide +kernel

private theorem gl_commute_gen {g : GL (Fin 2) (ZMod 3)}
    (hS : (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (autGenS : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      (autGenS : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (g : Matrix (Fin 2) (Fin 2) (ZMod 3)))
    (hT : (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (autGenT : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      (autGenT : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (g : Matrix (Fin 2) (Fin 2) (ZMod 3))) :
    g = 1 ∨ g = -1 := by
  have hdet : IsUnit (g : Matrix (Fin 2) (Fin 2) (ZMod 3)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  obtain ⟨u, hu⟩ := hdet.exists_right_inv
  rcases scalar_aux _ ⟨u, hu⟩ hS hT with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext (by rw [Units.val_neg, Units.val_one]; exact h))

theorem Aut.mem_center_gl3_iff (g : GL (Fin 2) (ZMod 3)) :
    g ∈ Subgroup.center (GL (Fin 2) (ZMod 3)) ↔ g = 1 ∨ g = -1 := by
  constructor
  · intro hg
    rw [Subgroup.mem_center_iff] at hg
    have h1 := congrArg (fun x : GL (Fin 2) (ZMod 3) => (x : Matrix (Fin 2) (Fin 2) (ZMod 3)))
      (hg (Matrix.SpecialLinearGroup.toGL autGenS))
    have h2 := congrArg (fun x : GL (Fin 2) (ZMod 3) => (x : Matrix (Fin 2) (Fin 2) (ZMod 3)))
      (hg (Matrix.SpecialLinearGroup.toGL autGenT))
    refine gl_commute_gen ?_ ?_
    · simpa using h1.symm
    · simpa using h2.symm
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · rw [Subgroup.mem_center_iff]
      intro h
      simp

theorem conjAut3_ker :
    (conjAut : GL (Fin 2) (ZMod 3) →* MulAut SL(2, ZMod 3)).ker =
      Subgroup.center (GL (Fin 2) (ZMod 3)) := by
  ext g
  rw [MonoidHom.mem_ker, Aut.mem_center_gl3_iff]
  constructor
  · intro hg
    have hc : ∀ b : SL(2, ZMod 3), (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
        (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) = (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
        (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
      intro b
      have h1 := congrArg (fun α : MulAut SL(2, ZMod 3) =>
        ((α b : SL(2, ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))) hg
      simp only [conjAut_apply, coe_conjSL, MulAut.one_apply] at h1
      calc (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (b : Matrix (Fin 2) (Fin 2) (ZMod 3))
          = (g * b * ((g⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))) *
            (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
              Units.val_one, Matrix.mul_one]
        _ = _ := by rw [h1]
    exact gl_commute_gen (hc autGenS) (hc autGenT)
  · rintro (rfl | rfl)
    · exact map_one _
    · ext b : 1
      apply Subtype.ext
      simp [conjAut_apply, coe_conjSL]

theorem Aut.natCard_gl2Three : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Matrix.card_GL_field (𝔽 := ZMod 3) 2]
  simp [Fin.prod_univ_two]

theorem Aut.orderOf_neg_one_gl3 : orderOf (-1 : GL (Fin 2) (ZMod 3)) = 2 := by
  refine orderOf_eq_prime (by simp) ?_
  intro h
  have := congrArg (fun x : GL (Fin 2) (ZMod 3) => (x : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0) h
  revert this
  simp
  decide

theorem Aut.natCard_center_gl3 : Nat.card (Subgroup.center (GL (Fin 2) (ZMod 3))) = 2 := by
  have : Subgroup.center (GL (Fin 2) (ZMod 3)) = Subgroup.zpowers (-1) := by
    ext g
    rw [Aut.mem_center_gl3_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
    · rintro ⟨k, rfl⟩
      rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · left
        rw [← two_mul, zpow_mul, zpow_two, neg_one_mul, neg_neg, one_zpow]
      · right
        rw [zpow_add_one, zpow_mul, zpow_two, neg_one_mul, neg_neg, one_zpow, one_mul]
  rw [this, Nat.card_zpowers, Aut.orderOf_neg_one_gl3]

theorem sl2Three_card_mulAut : Nat.card (MulAut SL(2, ZMod 3)) = 24 := by
  have h := Subgroup.card_ker_mul_card_range
    (conjAut : GL (Fin 2) (ZMod 3) →* MulAut SL(2, ZMod 3))
  rw [conjAut3_ker, Aut.natCard_center_gl3, Aut.natCard_gl2Three,
    MonoidHom.range_eq_top_of_surjective _ conjAut3_surjective, Subgroup.card_top] at h
  omega

end Ker

section PGL

@[expose] noncomputable def mulAutEquivPGL2 :
    MulAut SL(2, ZMod 3) ≃* PGL(2, ZMod 3) :=
  (QuotientGroup.quotientKerEquivOfSurjective
    (conjAut : GL (Fin 2) (ZMod 3) →* MulAut SL(2, ZMod 3)) conjAut3_surjective).symm.trans
    (QuotientGroup.quotientMulEquivOfEq conjAut3_ker)

theorem mulAutEquivPGL2_conjAut (g : GL (Fin 2) (ZMod 3)) :
    mulAutEquivPGL2 (conjAut g) = Matrix.ProjGenLinGroup.mk g := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective
      (conjAut : GL (Fin 2) (ZMod 3) →* MulAut SL(2, ZMod 3)) conjAut3_surjective).symm
      (conjAut g) = QuotientGroup.mk g := (MulEquiv.symm_apply_eq _).mpr rfl
  show (QuotientGroup.quotientMulEquivOfEq conjAut3_ker)
    ((QuotientGroup.quotientKerEquivOfSurjective
      (conjAut : GL (Fin 2) (ZMod 3) →* MulAut SL(2, ZMod 3)) conjAut3_surjective).symm
      (conjAut g)) = QuotientGroup.mk g
  rw [h]
  rfl

end PGL

end CFSG.ClassicalInvolution.Q3.Q3T6
