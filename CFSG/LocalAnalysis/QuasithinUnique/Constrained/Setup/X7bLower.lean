module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpMinor
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpCommon

public section

namespace CFSG.QuasithinUnique.Setup.X7b

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {K : Type} [Field K]

@[expose] def lowU (a b c d : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; a, 1, 0, 0; b, c, 1, 0; d, b + a * c, a, 1]

@[expose] def dmat (s t : K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.diagonal ![s, t, t⁻¹, s⁻¹]

theorem lowU_det (a b c d : K) : (lowU a b c d).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [lowU, Fin.prod_univ_four]
  · intro i j hij
    have hij' : i < j := hij
    fin_cases i <;> fin_cases j <;> simp_all [lowU]

@[expose] noncomputable def lowUGL (a b c d : K) : GL (Fin 4) K :=
  Matrix.GeneralLinearGroup.mk'' (lowU a b c d) (by rw [lowU_det]; exact isUnit_one)

theorem glMat_lowUGL (a b c d : K) : glMat (lowUGL a b c d) = lowU a b c d := rfl

theorem lowU_mul_lowU [CharP K 2] (a b c d A B C D : K) :
    lowU a b c d * lowU A B C D =
      lowU (a + A) (b + B + c * A) (c + C) (d + D + (b + a * c) * A + a * B) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowU, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | ring1 | (ring_nf; simp [h2])

theorem lowU_symp [CharP K 2] (a b c d : K) :
    (lowU a b c d)ᵀ * minorJ K * lowU a b c d = minorJ K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowU, minorJ_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four] <;>
    first | ring1 | (ring_nf; simp [h2])

theorem lowUGL_mem [CharP K 2] (a b c d : K) : lowUGL a b c d ∈ antiSp K := by
  rw [mem_antiSp]
  exact lowU_symp a b c d

@[expose] noncomputable def lowUSp [CharP K 2] (a b c d : K) : antiSp K :=
  ⟨lowUGL a b c d, lowUGL_mem a b c d⟩

theorem glMat_lowUSp [CharP K 2] (a b c d : K) :
    glMat ((lowUSp a b c d : antiSp K) : GL (Fin 4) K) = lowU a b c d := rfl

theorem lowUSp_mul [CharP K 2] (a b c d A B C D : K) :
    lowUSp a b c d * lowUSp A B C D =
      lowUSp (a + A) (b + B + c * A) (c + C) (d + D + (b + a * c) * A + a * B) :=
  Subtype.ext (Units.ext (lowU_mul_lowU a b c d A B C D))

theorem lowUSp_zero [CharP K 2] : lowUSp (0 : K) 0 0 0 = 1 := by
  refine Subtype.ext (Units.ext ?_)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [glMat_lowUSp, lowU]

theorem lowUSp_inv [CharP K 2] (a b c d : K) :
    (lowUSp a b c d)⁻¹ = lowUSp a (b + a * c) c d := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [inv_eq_iff_mul_eq_one, lowUSp_mul]
  have e1 : a + a = 0 := CharTwo.add_self_eq_zero a
  have e2 : b + (b + a * c) + c * a = 0 := by linear_combination (b + a * c) * h2
  have e3 : c + c = 0 := CharTwo.add_self_eq_zero c
  have e4 : d + d + (b + a * c) * a + a * (b + a * c) = 0 := by
    linear_combination (d + a * (b + a * c)) * h2
  rw [e1, e2, e3, e4]
  exact lowUSp_zero

variable (K) in
@[expose] def lowerUniSp [CharP K 2] : Subgroup (antiSp K) where
  carrier := {g | ∃ a b c d : K, g = lowUSp a b c d}
  one_mem' := ⟨0, 0, 0, 0, lowUSp_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, c, d, rfl⟩ ⟨A, B, C, D, rfl⟩
    exact ⟨_, _, _, _, lowUSp_mul a b c d A B C D⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, d, rfl⟩
    exact ⟨_, _, _, _, lowUSp_inv a b c d⟩

@[expose] def IsLowUni (M : Matrix (Fin 4) (Fin 4) K) : Prop :=
  (∀ i j : Fin 4, i < j → M i j = 0) ∧ ∀ i : Fin 4, M i i = 1

@[expose] def IsUpUni (M : Matrix (Fin 4) (Fin 4) K) : Prop :=
  (∀ i j : Fin 4, j < i → M i j = 0) ∧ ∀ i : Fin 4, M i i = 1

theorem isLowUni_lowU (a b c d : K) : IsLowUni (lowU a b c d) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [lowU]
  · fin_cases i <;> simp [lowU]

theorem mem_lowerUniSp_iff [CharP K 2] (g : antiSp K) :
    g ∈ lowerUniSp K ↔ IsLowUni (glMat (g : GL (Fin 4) K)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  constructor
  · rintro ⟨a, b, c, d, rfl⟩
    exact isLowUni_lowU a b c d
  · rintro ⟨hl, hd⟩
    have hg := mem_antiSp.mp g.2
    have h01 := congrFun (congrFun hg 0) 1
    have h02 := congrFun (congrFun hg 0) 2
    rw [transpose_mul_minorJ_mul_apply, minorJ_apply] at h01 h02
    refine ⟨glMat (g : GL (Fin 4) K) 1 0, glMat (g : GL (Fin 4) K) 2 0,
      glMat (g : GL (Fin 4) K) 2 1, glMat (g : GL (Fin 4) K) 3 0, ?_⟩
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    have e1 := hl 0 1 (by decide)
    have e2 := hl 0 2 (by decide)
    have e3 := hl 0 3 (by decide)
    have e4 := hl 1 2 (by decide)
    have e5 := hl 1 3 (by decide)
    have e6 := hl 2 3 (by decide)
    have d0 := hd 0
    have d1 := hd 1
    have d2 := hd 2
    have d3 := hd 3
    simp only [glMat_lowUSp, lowU]
    set m := glMat (g : GL (Fin 4) K) with hm
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one] <;>
      first
      | ring1
      | linear_combination h01 + (-(glMat (g : GL (Fin 4) K) 2 0 +
          glMat (g : GL (Fin 4) K) 1 0 * glMat (g : GL (Fin 4) K) 2 1)) * h2
      | linear_combination h02 + (-(glMat (g : GL (Fin 4) K) 1 0)) * h2

theorem lowUSp_inj [CharP K 2] {a b c d A B C D : K} (h : lowUSp a b c d = lowUSp A B C D) :
    a = A ∧ b = B ∧ c = C ∧ d = D := by
  have h1 := congrArg (fun g : antiSp K => glMat (g : GL (Fin 4) K)) h
  simp only [glMat_lowUSp] at h1
  have e10 := congrFun (congrFun h1 1) 0
  have e20 := congrFun (congrFun h1 2) 0
  have e21 := congrFun (congrFun h1 2) 1
  have e30 := congrFun (congrFun h1 3) 0
  simp [lowU] at e10 e20 e21 e30
  exact ⟨e10, e20, e21, e30⟩

theorem lowUMap_bijective [CharP K 2] :
    Function.Bijective (fun p : K × K × K × K =>
      (⟨lowUSp p.1 p.2.1 p.2.2.1 p.2.2.2, p.1, p.2.1, p.2.2.1, p.2.2.2, rfl⟩ : lowerUniSp K)) := by
  constructor
  · intro p q h
    obtain ⟨h1, h2, h3, h4⟩ := lowUSp_inj (congrArg Subtype.val h)
    exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))
  · rintro ⟨g, a, b, c, d, hg⟩
    exact ⟨(a, b, c, d), Subtype.ext hg.symm⟩

theorem minorMap_lowU [CharP K 2] (a b c d : K) :
    minorMap (lowU a b c d) = lowU c (d + a * b + a ^ 2 * c) (a ^ 2) (b ^ 2 + a * b * c + c * d) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minorMap_apply, minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three, lowU,
      CharTwo.sub_eq_add] <;>
    first | ring1 | (ring_nf; simp [h2])

theorem minorMap_minorMap_lowU [CharP K 2] (a b c d : K) :
    minorMap (minorMap (lowU a b c d)) = lowU (a ^ 2) (b ^ 2) (c ^ 2) (d ^ 2) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h4 : (4 : K) = 0 := by rw [show (4 : K) = 2 * 2 by norm_num, h2, zero_mul]
  rw [minorMap_lowU, minorMap_lowU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowU] <;> first | ring1 | (ring_nf; simp [h2, h4])

theorem minorMap_minorJ [CharP K 2] : minorMap (minorJ K) = minorJ K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minorMap_apply, minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three, minorJ_apply,
      CharTwo.neg_eq]

theorem minorMap_dmat (s t : K) :
    minorMap (dmat s t) = dmat (s * t) (s * t⁻¹) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minorMap_apply, minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three, dmat]

theorem minorMap_minorMap_dmat {s t : K} (hs : s ≠ 0) (ht : t ≠ 0) :
    minorMap (minorMap (dmat s t)) = dmat (s ^ 2) (t ^ 2) := by
  rw [minorMap_dmat, minorMap_dmat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dmat] <;> field_simp

@[expose] noncomputable def Jgl : GL (Fin 4) K :=
  Matrix.GeneralLinearGroup.mk'' (minorJ K) (isUnit_iff_ne_zero.mpr det_minorJ_ne_zero)

theorem glMat_Jgl : glMat (Jgl : GL (Fin 4) K) = minorJ K := rfl

theorem Jgl_mem : (Jgl : GL (Fin 4) K) ∈ antiSp K := by
  rw [mem_antiSp, glMat_Jgl, minorJ_transpose, minorJ_mul_self, Matrix.one_mul]

@[expose] noncomputable def Jsp : antiSp K := ⟨Jgl, Jgl_mem⟩

theorem glMat_Jsp : glMat ((Jsp : antiSp K) : GL (Fin 4) K) = minorJ K := rfl

theorem Jsp_mul_self : (Jsp : antiSp K) * Jsp = 1 :=
  Subtype.ext (Units.ext minorJ_mul_self)

theorem Jsp_inv : (Jsp : antiSp K)⁻¹ = Jsp := inv_eq_of_mul_eq_one_right Jsp_mul_self

theorem minorJ_mul_mul_minorJ_apply (M : Matrix (Fin 4) (Fin 4) K) (i j : Fin 4) :
    (minorJ K * M * minorJ K) i j = M i.rev j.rev := by
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, minorJ_apply]

theorem glMat_Jsp_conj (g : antiSp K) :
    glMat (((Jsp * g * Jsp : antiSp K)) : GL (Fin 4) K) =
      minorJ K * glMat (g : GL (Fin 4) K) * minorJ K := rfl

variable (K) in
@[expose] noncomputable def upperUniSp [CharP K 2] : Subgroup (antiSp K) :=
  (lowerUniSp K).map (MulAut.conj (Jsp : antiSp K)).toMonoidHom

theorem mem_upperUniSp_iff [CharP K 2] (g : antiSp K) :
    g ∈ upperUniSp K ↔ IsUpUni (glMat (g : GL (Fin 4) K)) := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hl := (mem_lowerUniSp_iff h).mp hh
    show IsUpUni (glMat (((Jsp * h * Jsp⁻¹ : antiSp K)) : GL (Fin 4) K))
    rw [Jsp_inv, glMat_Jsp_conj]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [minorJ_mul_mul_minorJ_apply]
      exact hl.1 _ _ (by simpa using hij)
    · rw [minorJ_mul_mul_minorJ_apply]
      exact hl.2 _
  · intro hg
    have hmem : Jsp * g * Jsp ∈ lowerUniSp K := by
      rw [mem_lowerUniSp_iff, glMat_Jsp_conj]
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · rw [minorJ_mul_mul_minorJ_apply]
        exact hg.1 _ _ (by simpa using hij)
      · rw [minorJ_mul_mul_minorJ_apply]
        exact hg.2 _
    refine ⟨Jsp * g * Jsp, hmem, ?_⟩
    show Jsp * (Jsp * g * Jsp) * Jsp⁻¹ = g
    rw [Jsp_inv]
    calc Jsp * (Jsp * g * Jsp) * Jsp = (Jsp * Jsp) * g * (Jsp * Jsp) := by group
      _ = g := by rw [Jsp_mul_self]; simp

theorem upperUniSp_eq_map [CharP K 2] :
    upperUniSp K = (lowerUniSp K).map (MulAut.conj (Jsp : antiSp K)).toMonoidHom := rfl

theorem minorHom_lowUSp [CharP K 2] (a b c d : K) :
    minorHom K (lowUSp a b c d) =
      lowUSp c (d + a * b + a ^ 2 * c) (a ^ 2) (b ^ 2 + a * b * c + c * d) :=
  Subtype.ext (Units.ext (by
    show minorMap (lowU a b c d) = lowU _ _ _ _
    exact minorMap_lowU a b c d))

theorem minorHom_minorHom_lowUSp [CharP K 2] (a b c d : K) :
    minorHom K (minorHom K (lowUSp a b c d)) = lowUSp (a ^ 2) (b ^ 2) (c ^ 2) (d ^ 2) := by
  rw [minorHom_lowUSp, minorHom_lowUSp]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h4 : (4 : K) = 0 := by rw [show (4 : K) = 2 * 2 by norm_num, h2, zero_mul]
  congr 1 <;> first | ring1 | (ring_nf; simp [h2, h4])

theorem minorHom_Jsp [CharP K 2] : minorHom K (Jsp : antiSp K) = Jsp :=
  Subtype.ext (Units.ext minorMap_minorJ)

theorem minorHom_lowerUniSp_le [CharP K 2] :
    (lowerUniSp K).map (minorHom K) ≤ lowerUniSp K := by
  rintro _ ⟨_, ⟨a, b, c, d, rfl⟩, rfl⟩
  rw [minorHom_lowUSp]
  exact ⟨_, _, _, _, rfl⟩

theorem minorHom_upperUniSp_le [CharP K 2] :
    (upperUniSp K).map (minorHom K) ≤ upperUniSp K := by
  rintro _ ⟨_, ⟨h, hh, rfl⟩, rfl⟩
  refine ⟨minorHom K h, minorHom_lowerUniSp_le ⟨h, hh, rfl⟩, ?_⟩
  show Jsp * minorHom K h * Jsp⁻¹ = minorHom K (Jsp * h * Jsp⁻¹)
  rw [map_mul, map_mul, map_inv, minorHom_Jsp]

@[expose] noncomputable def dGL (s t : Kˣ) : GL (Fin 4) K :=
  Matrix.GeneralLinearGroup.mk'' (dmat (s : K) (t : K)) (by
    rw [dmat, Matrix.det_diagonal, Fin.prod_univ_four]
    simp)

theorem glMat_dGL (s t : Kˣ) : glMat (dGL s t : GL (Fin 4) K) = dmat (s : K) (t : K) := rfl

theorem dGL_mem [CharP K 2] (s t : Kˣ) : (dGL s t : GL (Fin 4) K) ∈ antiSp K := by
  rw [mem_antiSp, glMat_dGL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dmat, Matrix.mul_apply, Fin.sum_univ_four, minorJ_apply, Matrix.diagonal_apply]

@[expose] noncomputable def dSp [CharP K 2] (s t : Kˣ) : antiSp K := ⟨dGL s t, dGL_mem s t⟩

theorem minorHom_dSp [CharP K 2] (s t : Kˣ) : minorHom K (dSp s t) = dSp (s * t) (s * t⁻¹) :=
  Subtype.ext (Units.ext (by
    show minorMap (dmat (s : K) (t : K)) = dmat _ _
    rw [minorMap_dmat]
    simp [dmat]))

theorem minorHom_minorHom_dSp [CharP K 2] (s t : Kˣ) :
    minorHom K (minorHom K (dSp s t)) = dSp (s ^ 2) (t ^ 2) := by
  rw [minorHom_dSp, minorHom_dSp]
  congr 1
  · apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    field_simp
  · apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    field_simp

theorem card_lowerUniSp [CharP K 2] [Finite K] : Nat.card (lowerUniSp K) = Nat.card K ^ 4 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ lowUMap_bijective)]
  simp [Nat.card_prod, pow_succ]
  ring

theorem card_upperUniSp [CharP K 2] [Finite K] : Nat.card (upperUniSp K) = Nat.card K ^ 4 := by
  rw [upperUniSp, Subgroup.card_map_of_injective (MulAut.conj (Jsp : antiSp K)).injective]
  exact card_lowerUniSp

theorem isPGroup_lowerUniSp [CharP K 2] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    IsPGroup 2 (lowerUniSp K) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  IsPGroup.of_card (n := f * 4) (by rw [card_lowerUniSp, hK, pow_mul])

theorem isPGroup_upperUniSp [CharP K 2] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    IsPGroup 2 (upperUniSp K) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  IsPGroup.of_card (n := f * 4) (by rw [card_upperUniSp, hK, pow_mul])

theorem lower_unipotent_minor_coordinates [CharP K 2] :
    Function.Bijective (fun p : K × K × K × K =>
      (⟨lowUSp p.1 p.2.1 p.2.2.1 p.2.2.2, p.1, p.2.1, p.2.2.1, p.2.2.2, rfl⟩ : lowerUniSp K)) ∧
    (∀ g : antiSp K, g ∈ lowerUniSp K ↔ IsLowUni (glMat (g : GL (Fin 4) K))) ∧
    (∀ g : antiSp K, g ∈ upperUniSp K ↔ IsUpUni (glMat (g : GL (Fin 4) K))) ∧
    (Jsp : antiSp K) * Jsp = 1 ∧
    upperUniSp K = (lowerUniSp K).map (MulAut.conj (Jsp : antiSp K)).toMonoidHom ∧
    minorMap (minorJ K) = minorJ K ∧
    (lowerUniSp K).map (minorHom K) ≤ lowerUniSp K ∧
    (upperUniSp K).map (minorHom K) ≤ upperUniSp K ∧
    (∀ a b c d : K, minorMap (lowU a b c d) =
      lowU c (d + a * b + a ^ 2 * c) (a ^ 2) (b ^ 2 + a * b * c + c * d)) ∧
    (∀ a b c d : K, minorMap (minorMap (lowU a b c d)) = lowU (a ^ 2) (b ^ 2) (c ^ 2) (d ^ 2)) ∧
    (∀ s t : Kˣ, minorHom K (dSp s t) = dSp (s * t) (s * t⁻¹) ∧
      minorHom K (minorHom K (dSp s t)) = dSp (s ^ 2) (t ^ 2)) :=
  ⟨lowUMap_bijective, mem_lowerUniSp_iff, mem_upperUniSp_iff, Jsp_mul_self, upperUniSp_eq_map,
    minorMap_minorJ, minorHom_lowerUniSp_le, minorHom_upperUniSp_le, minorMap_lowU,
    minorMap_minorMap_lowU, fun s t => ⟨minorHom_dSp s t, minorHom_minorHom_dSp s t⟩⟩

theorem lower_unipotent_minor_coordinates_finite [CharP K 2] [Finite K] :
    Nat.card (lowerUniSp K) = Nat.card K ^ 4 ∧ Nat.card (upperUniSp K) = Nat.card K ^ 4 ∧
      IsPGroup 2 (lowerUniSp K) ∧ IsPGroup 2 (upperUniSp K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [← Nat.card_eq_fintype_card] at hn
  exact ⟨card_lowerUniSp, card_upperUniSp, isPGroup_lowerUniSp hn, isPGroup_upperUniSp hn⟩

end CFSG.QuasithinUnique.Setup.X7b
