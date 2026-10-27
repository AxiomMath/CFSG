module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoGeneralLinear
public import CFSG.CharacterTheory.Semidihedral.QuaternionAutomorphismLifting

public section

namespace CFSG.Semidihedral.MatrixCoverData

noncomputable section

open Matrix
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

universe u

variable (F : Type u) [Field F]

abbrev SL := SpecialLinearGroup (Fin 2) F

abbrev GL2 := GeneralLinearGroup (Fin 2) F

abbrev C2 := Multiplicative (ZMod 2)

@[expose] def exponent (e : C2) : ℕ := (Multiplicative.toAdd e).val

theorem exponent_lt_two (e : C2) : exponent e < 2 := ZMod.val_lt _

theorem exponent_mul (e d : C2) :
    exponent (e * d) = (exponent e + exponent d) % 2 := ZMod.val_add _ _

@[expose] def J (a : Fˣ) : GL2 F :=
  GeneralLinearGroup.mkOfDetNeZero !![0, -(a : F); 1, 0] (by
    simp [Matrix.det_fin_two])

theorem J_matrix (a : Fˣ) :
    (J F a : Matrix (Fin 2) (Fin 2) F) = !![0, -(a : F); 1, 0] := rfl

theorem J_det (a : Fˣ) : GeneralLinearGroup.det (J F a) = a := by
  apply Units.ext
  simp [J, Matrix.det_fin_two]

theorem J_square (a : Fˣ) :
    (J F a) ^ 2 = GeneralLinearGroup.scalar (Fin 2) (-a) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def slConjugation : GL2 F →* MulAut (SL F) :=
  (MulAut.congr (SpecialLinearGroup.toGLKerEquiv (n := Fin 2) (R := F)).symm).toMonoidHom.comp (MulAut.conjNormal (H := GeneralLinearGroup.det.ker))

theorem slConjugation_toGL (g : GL2 F) (X : SL F) :
    SpecialLinearGroup.toGL (slConjugation F g X) =
      g * SpecialLinearGroup.toGL X * g⁻¹ := by
  let e := SpecialLinearGroup.toGLKerEquiv (n := Fin 2) (R := F)
  change ((e (slConjugation F g X) : GeneralLinearGroup.det.ker) : GL2 F) = _
  have he : e (slConjugation F g X) =
      MulAut.conjNormal g (e X) := by
    change e (e.symm (MulAut.conjNormal g (e X))) = _
    exact e.apply_symm_apply _
  rw [he, MulAut.conjNormal_apply]
  rfl

theorem slConjugation_matrix (g : GL2 F) (X : SL F) :
    (slConjugation F g X : Matrix (Fin 2) (Fin 2) F) =
      (g : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F) *
        (g⁻¹ : GL2 F) :=
  congrArg Units.val (slConjugation_toGL F g X)

@[expose] def beta (a : Fˣ) : MulAut (SL F) := slConjugation F (J F a)

theorem beta_square (a : Fˣ) : (beta F a) ^ 2 = 1 := by
  apply MulEquiv.ext
  intro X
  apply SpecialLinearGroup.toGL_injective
  change SpecialLinearGroup.toGL (slConjugation F (J F a)
    (slConjugation F (J F a) X)) = SpecialLinearGroup.toGL X
  rw [slConjugation_toGL, slConjugation_toGL]
  calc
    J F a * (J F a * SpecialLinearGroup.toGL X * (J F a)⁻¹) * (J F a)⁻¹ =
        (J F a) ^ 2 * SpecialLinearGroup.toGL X * ((J F a) ^ 2)⁻¹ := by simp only [pow_two]; group
    _ = SpecialLinearGroup.toGL X := by
      rw [J_square, GeneralLinearGroup.scalar_commute]
      group

theorem field_map_J (sigma : F ≃+* F) (a : Fˣ) :
    GeneralLinearGroup.map sigma.toRingHom (J F a) =
      J F (Units.map sigma.toMonoidHom a) := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.map_apply, J]

theorem toGL_field_map (sigma : F ≃+* F) (X : SL F) :
    SpecialLinearGroup.toGL (SpecialLinearGroup.map sigma.toRingHom X) =
      GeneralLinearGroup.map sigma.toRingHom (SpecialLinearGroup.toGL X) :=
  Units.ext rfl

theorem field_map_conjugation (sigma : F ≃+* F) (g : GL2 F) (X : SL F) :
    SpecialLinearGroup.map sigma.toRingHom (slConjugation F g X) =
      slConjugation F (GeneralLinearGroup.map sigma.toRingHom g)
        (SpecialLinearGroup.map sigma.toRingHom X) := by
  apply SpecialLinearGroup.toGL_injective
  rw [toGL_field_map, slConjugation_toGL, map_mul, map_mul, map_inv,
    slConjugation_toGL, toGL_field_map]

theorem field_map_beta (sigma : F ≃+* F) (a : Fˣ) (X : SL F) :
    SpecialLinearGroup.map sigma.toRingHom (beta F a X) =
      beta F (Units.map sigma.toMonoidHom a) (SpecialLinearGroup.map sigma.toRingHom X) := by
  rw [beta, field_map_conjugation, field_map_J]
  rfl

theorem field_map_beta_of_fix (sigma : F ≃+* F) (a : Fˣ)
    (ha : sigma (a : F) = a) (X : SL F) :
    SpecialLinearGroup.map sigma.toRingHom (beta F a X) =
      beta F a (SpecialLinearGroup.map sigma.toRingHom X) := by
  have h : Units.map sigma.toMonoidHom a = a := Units.ext ha
  rw [field_map_beta, h]

@[expose] def action (a : Fˣ) : C2 →* MulAut (SL F) :=
  QuaternionAutomorphismLifting.coordinatePowerHom 2 (beta F a) (beta_square F a)

theorem action_zero (a : Fˣ) :
    action F a (Multiplicative.ofAdd (0 : ZMod 2)) = 1 := map_one _

theorem action_one (a : Fˣ) :
    action F a (Multiplicative.ofAdd (1 : ZMod 2)) = beta F a := by
  simpa only [action, pow_one, Nat.cast_one] using
    QuaternionAutomorphismLifting.coordinatePowerHom_natCast 2
      (beta F a) (beta_square F a) 1

theorem action_toGL (a : Fˣ) (e : C2) (X : SL F) :
    SpecialLinearGroup.toGL (action F a e X) =
      (J F a) ^ exponent e * SpecialLinearGroup.toGL X *
        ((J F a) ^ exponent e)⁻¹ := by
  change SpecialLinearGroup.toGL (((slConjugation F (J F a)) ^ exponent e) X) = _
  rw [← map_pow]
  exact slConjugation_toGL F _ X

abbrev M (a : Fˣ) := SemidirectProduct (SL F) C2 (action F a)

theorem multiplication (a : Fˣ) (X Y : SL F) (e d : C2) :
    (⟨X, e⟩ : M F a) * ⟨Y, d⟩ = ⟨X * action F a e Y, e * d⟩ := rfl

theorem multiplication_matrix (a : Fˣ) (x y : M F a) :
    ((x * y).left : Matrix (Fin 2) (Fin 2) F) =
      (x.left : Matrix (Fin 2) (Fin 2) F) *
        ((J F a) ^ exponent x.right : GL2 F) *
        (y.left : Matrix (Fin 2) (Fin 2) F) *
        (((J F a) ^ exponent x.right)⁻¹ : GL2 F) := by
  have h : (action F a x.right y.left : Matrix (Fin 2) (Fin 2) F) =
      ((J F a) ^ exponent x.right : GL2 F) *
        (y.left : Matrix (Fin 2) (Fin 2) F) *
        (((J F a) ^ exponent x.right)⁻¹ : GL2 F) :=
    congrArg Units.val (action_toGL F a x.right y.left)
  change (x.left : Matrix (Fin 2) (Fin 2) F) * (action F a x.right y.left :
    Matrix (Fin 2) (Fin 2) F) = _
  rw [h]
  simp only [Matrix.mul_assoc]

@[expose] def inclusion (a : Fˣ) : SL F →* M F a := SemidirectProduct.inl

theorem inclusion_injective (a : Fˣ) : Function.Injective (inclusion F a) :=
  SemidirectProduct.inl_injective

theorem inclusion_pair (a : Fˣ) (X : SL F) :
    inclusion F a X = ⟨X, Multiplicative.ofAdd (0 : ZMod 2)⟩ := rfl

@[expose] def u (a : Fˣ) : M F a :=
  SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))

theorem u_pair (a : Fˣ) :
    u F a = ⟨1, Multiplicative.ofAdd (1 : ZMod 2)⟩ := rfl

theorem u_square (a : Fˣ) : (u F a) ^ 2 = 1 := by
  change (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)) : M F a) ^ 2 = 1
  rw [← map_pow]
  have h : (Multiplicative.ofAdd (1 : ZMod 2) : C2) ^ 2 = 1 := by decide
  rw [h, map_one]

@[expose] def glProjective : GL2 F →* coordinateD F where
  toFun g := ⟨coordinatePGLAction F (Matrix.ProjGenLinGroup.mk g), by
    rw [← coordinatePGLAction_range_eq_D]
    exact ⟨_, rfl⟩⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp)

theorem glProjective_coe (g : GL2 F) :
    (glProjective F g : Equiv.Perm (Omega F)) =
      coordinatePGLAction F (Matrix.ProjGenLinGroup.mk g) := rfl

theorem glProjective_scalar (c : Fˣ) :
    glProjective F (GeneralLinearGroup.scalar (Fin 2) c) = 1 := by
  apply Subtype.ext
  simp [glProjective]

@[expose] def slProjective : SL F →* coordinateD F :=
  (glProjective F).comp SpecialLinearGroup.toGL

@[expose] def jProjective (a : Fˣ) : coordinateD F := glProjective F (J F a)

theorem jProjective_square (a : Fˣ) : (jProjective F a) ^ 2 = 1 := by
  rw [jProjective, ← map_pow, J_square, glProjective_scalar]

@[expose] def c2Projective (a : Fˣ) : C2 →* coordinateD F :=
  QuaternionAutomorphismLifting.coordinatePowerHom 2 (jProjective F a)
    (jProjective_square F a)

theorem projective_action (a : Fˣ) (e : C2) (X : SL F) :
    slProjective F (action F a e X) =
      c2Projective F a e * slProjective F X * (c2Projective F a e)⁻¹ := by
  change glProjective F (SpecialLinearGroup.toGL (action F a e X)) = _
  rw [action_toGL, map_mul, map_mul, map_inv, map_pow]
  rfl

@[expose] def pi (a : Fˣ) : M F a →* coordinateD F :=
  SemidirectProduct.lift (slProjective F) (c2Projective F a) (by
    intro e
    apply MonoidHom.ext
    intro X
    exact projective_action F a e X)

theorem pi_formula (a : Fˣ) (x : M F a) :
    pi F a x = glProjective F
      (SpecialLinearGroup.toGL x.left * (J F a) ^ exponent x.right) := by
  change slProjective F x.left * c2Projective F a x.right = _
  rw [map_mul, map_pow]
  rfl

theorem pi_coordinate (a : Fˣ) (x : M F a) :
    (pi F a x : Equiv.Perm (Omega F)) = coordinatePGLAction F
      (Matrix.ProjGenLinGroup.mk
        (SpecialLinearGroup.toGL x.left * (J F a) ^ exponent x.right)) := by
  rw [pi_formula, glProjective_coe]

theorem pi_inclusion (a : Fˣ) (X : SL F) :
    pi F a (inclusion F a X) = slProjective F X :=
  SemidirectProduct.lift_inl _ _ _ _

theorem pi_u (a : Fˣ) : pi F a (u F a) = jProjective F a := by
  change (SemidirectProduct.lift _ _ _) (SemidirectProduct.inr _) = _
  rw [SemidirectProduct.lift_inr]
  simpa only [c2Projective, pow_one, Nat.cast_one] using
    QuaternionAutomorphismLifting.coordinatePowerHom_natCast 2
      (jProjective F a) (jProjective_square F a) 1

theorem nonsquare_involution_linear_two_cover_data (a : Fˣ) :
    (J F a : Matrix (Fin 2) (Fin 2) F) = !![0, -(a : F); 1, 0] ∧
    GeneralLinearGroup.det (J F a) = a ∧
    (J F a) ^ 2 = GeneralLinearGroup.scalar (Fin 2) (-a) ∧
    (∀ X : SL F, (beta F a X : Matrix (Fin 2) (Fin 2) F) =
      (J F a : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F) *
        ((J F a)⁻¹ : GL2 F)) ∧
    (beta F a) ^ 2 = 1 ∧
    (∀ x y : M F a, (x * y).right = x.right * y.right ∧
      ((x * y).left : Matrix (Fin 2) (Fin 2) F) =
        (x.left : Matrix (Fin 2) (Fin 2) F) *
          ((J F a) ^ exponent x.right : GL2 F) *
          (y.left : Matrix (Fin 2) (Fin 2) F) *
          (((J F a) ^ exponent x.right)⁻¹ : GL2 F)) ∧
    Function.Injective (inclusion F a) ∧
    (∀ X : SL F, inclusion F a X = ⟨X, Multiplicative.ofAdd (0 : ZMod 2)⟩) ∧
    u F a = ⟨1, Multiplicative.ofAdd (1 : ZMod 2)⟩ ∧
    (∀ x : M F a, (pi F a x : Equiv.Perm (Omega F)) = coordinatePGLAction F
      (Matrix.ProjGenLinGroup.mk
        (SpecialLinearGroup.toGL x.left * (J F a) ^ exponent x.right))) := by
  exact ⟨J_matrix F a, J_det F a, J_square F a,
    slConjugation_matrix F (J F a), beta_square F a,
    fun x y => ⟨rfl, multiplication_matrix F a x y⟩,
    inclusion_injective F a, inclusion_pair F a, u_pair F a, pi_coordinate F a⟩

end

end CFSG.Semidihedral.MatrixCoverData
