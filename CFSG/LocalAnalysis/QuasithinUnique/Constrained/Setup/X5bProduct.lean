module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bField
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bZsig
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport

public section

open Matrix Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

namespace CFSG.QuasithinUnique.Setup.X5

section Identities

variable {K : Type} [Field K]

@[expose] def cM (a b : K) : Matrix (Fin 3) (Fin 3) K := !![0, a, 1; b, 0, a; 1, b, 0]
@[expose] def cT1 (a : K) : Matrix (Fin 3) (Fin 3) K := !![1, a, 1; 0, 1, 0; 0, 0, 1]
@[expose] def cT2 (a b : K) : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; b, 1, a; 0, 0, 1]
@[expose] def cT3 (b : K) : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, 1, 0; 1, b, 1]
@[expose] def cP : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
@[expose] def cG (a b : K) : Matrix (Fin 3) (Fin 3) K := cT1 a * cT2 a b * cT3 b

theorem cT1_sq (a : K) (h2 : (2 : K) = 0) :
    cT1 a * cT1 a = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cT1, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    first | linear_combination (a) * h2 | linear_combination (1) * h2

theorem cT2_sq (a b : K) (h2 : (2 : K) = 0) :
    cT2 a b * cT2 a b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cT2, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    first | linear_combination (a) * h2 | linear_combination (b) * h2

theorem cT3_sq (b : K) (h2 : (2 : K) = 0) :
    cT3 b * cT3 b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cT3, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    first | linear_combination (1) * h2 | linear_combination (b) * h2

theorem cT1_iso (a b : K) (h2 : (2 : K) = 0) :
    (cT1 b)ᵀ * cM a b * cT1 a = cM a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cT1, cM, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    first | linear_combination (a) * h2 | linear_combination (1) * h2 | linear_combination (b) * h2 | linear_combination (a*b) * h2

theorem cT2_iso (a b : K) (h2 : (2 : K) = 0) :
    (cT2 b a)ᵀ * cM a b * cT2 a b = cM a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cT2, cM, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    first | linear_combination (b^2) * h2 | linear_combination (a^2) * h2 | linear_combination (a*b) * h2

theorem cT3_iso (a b : K) (h2 : (2 : K) = 0) :
    (cT3 a)ᵀ * cM a b * cT3 b = cM a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cT3, cM, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    first | linear_combination (1) * h2 | linear_combination (a) * h2 | linear_combination (b) * h2 | linear_combination (a*b) * h2

theorem cP_cM_cP (a b : K) :
    cP * cM a b * cP = cM b a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cP, cM, Matrix.mul_apply, Fin.sum_univ_succ]

theorem cP_cT1_cP (b : K) :
    cP * cT1 b * cP = cT3 b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cP, cT1, cT3, Matrix.mul_apply, Fin.sum_univ_succ]

theorem cP_cT2_cP (a b : K) :
    cP * cT2 b a * cP = cT2 a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cP, cT2, Matrix.mul_apply, Fin.sum_univ_succ]

theorem cP_cT3_cP (a : K) :
    cP * cT3 a * cP = cT1 a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cP, cT3, cT1, Matrix.mul_apply, Fin.sum_univ_succ]

theorem cG_charpoly (a b : K) (h2 : (2 : K) = 0) :
    cG a b ^ 3 + (a ^ 2) • cG a b ^ 2 + (b ^ 2) • cG a b + 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cG, cT1, cT2, cT3, pow_succ] <;>
    first | linear_combination (a^4 + 2*a^3*b + a^2*b^2 + 4*a^2 + 3*a*b + b^2 + 3) * h2 | linear_combination (a^4 + 3*a^3*b + 3*a^2*b^2 + 5*a^2 + a*b^3 + 6*a*b + 3*b^2 + 4) * h2 | linear_combination (a^5 + 3*a^4*b + 2*a^3*b^2 + 5*a^3 + 7*a^2*b + 2*a*b^2 + 4*a + 2*b) * h2 | linear_combination (a^4*b + 2*a^3*b^2 + a^3 + a^2*b^3 + 6*a^2*b + 4*a*b^2 + 2*a + b^3 + 4*b) * h2 | linear_combination (a^6 + 3*a^5*b + 2*a^4*b^2 + 7*a^4 + 10*a^3*b + 3*a^2*b^2 + 11*a^2 + 6*a*b + b^2 + 4) * h2 | linear_combination (a^5 + 4*a^4*b + 5*a^3*b^2 + 6*a^3 + 2*a^2*b^3 + 12*a^2*b + 7*a*b^2 + 6*a + b^3 + 4*b) * h2 | linear_combination (a^5*b + 3*a^4*b^2 + a^4 + 2*a^3*b^3 + 8*a^3*b + 9*a^2*b^2 + 3*a^2 + 2*a*b^3 + 8*a*b + 3*b^2 + 1) * h2 | linear_combination (a^6 + 4*a^5*b + 5*a^4*b^2 + 8*a^4 + 2*a^3*b^3 + 17*a^3*b + 11*a^2*b^2 + 15*a^2 + 2*a*b^3 + 13*a*b + 4*b^2 + 7) * h2 | linear_combination (a^6*b + 3*a^5*b^2 + a^5 + 2*a^4*b^3 + 10*a^4*b + 12*a^3*b^2 + 5*a^3 + 3*a^2*b^3 + 18*a^2*b + 8*a*b^2 + 4*a + b^3 + 6*b) * h2

theorem det_cM (a b : K) : (cM a b).det = a ^ 2 + b ^ 2 := by
  rw [cM, Matrix.det_fin_three]
  simp
  ring

theorem det_cT1 (a : K) : (cT1 a).det = 1 := by
  rw [cT1, Matrix.det_fin_three]
  simp

theorem det_cT2 (a b : K) : (cT2 a b).det = 1 := by
  rw [cT2, Matrix.det_fin_three]
  simp

theorem det_cT3 (b : K) : (cT3 b).det = 1 := by
  rw [cT3, Matrix.det_fin_three]
  simp

end Identities

section BarMaps

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem map_cM (a b : K) : (cM a b).map h.bar = cM (h.bar a) (h.bar b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cM]

theorem map_cT1 (a : K) : (cT1 a).map h.bar = cT1 (h.bar a) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cT1]

theorem map_cT2 (a b : K) : (cT2 a b).map h.bar = cT2 (h.bar a) (h.bar b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cT2]

theorem map_cT3 (b : K) : (cT3 b).map h.bar = cT3 (h.bar b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cT3]

theorem map_cP : (cP : Matrix (Fin 3) (Fin 3) K).map h.bar = cP := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cP]

theorem cM_hermitian (a : K) : ((cM a (h.bar a)).map h.bar)ᵀ = cM a (h.bar a) := by
  rw [map_cM, h.bar_bar]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cM]

end BarMaps

section Orthonormalizer

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem exists_orthonormalizer {M : Matrix (Fin 3) (Fin 3) K} (hM : (M.map h.bar)ᵀ = M)
    (hdet : M.det ≠ 0) :
    ∃ H : GL (Fin 3) K, ((H : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * M * H = 1 := by
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis (gramForm_isSymm h hM)
    (gramForm_separatingLeft h hdet)
  have hr : Module.finrank K (Fin 3 → K) = 3 := Module.finrank_fin_fun K
  let e' : Module.Basis (Fin 3) K (Fin 3 → K) := e.reindex (finCongr hr)
  let Hm : Matrix (Fin 3) (Fin 3) K := Matrix.of fun k i => e' i k
  have hcol : ∀ i, Hm *ᵥ Pi.single i 1 = e' i := fun i => by
    ext k
    simp [Hm]
  have hHm : (Hm.map h.bar)ᵀ * M * Hm = 1 := by
    ext i j
    have h1 := gramForm_mulVec h M Hm (Pi.single i 1) (Pi.single j 1)
    rw [gramForm_single, hcol, hcol] at h1
    rw [← h1]
    have := he ((finCongr hr).symm i) ((finCongr hr).symm j)
    simp only [e', Module.Basis.reindex_apply] at this ⊢
    rw [this]
    simp [Matrix.one_apply]
  have hdetH : Hm.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hHm
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  exact ⟨Matrix.GeneralLinearGroup.mk'' Hm (isUnit_iff_ne_zero.mpr hdetH), hHm⟩

end Orthonormalizer

section Core

variable {f : ℕ} {K : Type} [Field K]

theorem exists_core (h : UnitaryFieldData 2 f K) (hf : 1 ≤ f) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hord : orderOf (2 : ZMod ℓ) = 6 * f) :
    ∃ a : K, a ^ 2 + (h.bar a) ^ 2 ≠ 0 ∧ cG a (h.bar a) ^ ℓ = 1 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK2 : CharP K 2 := h.charP
  have : Finite K := h.finite
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨hx6, hquad⟩ := orderOf_and_quad_of_orderOf_two hf hord
  obtain ⟨τ, hne, hdvd⟩ := exists_cubic_factor h hℓ hord hx6 hquad
  obtain ⟨a, ha⟩ : IsSquare τ := FiniteField.isSquare_of_char_two (by
    rw [ringChar.eq K 2]) τ
  have hτb : h.bar τ = h.bar a * h.bar a := by rw [ha, map_mul]
  refine ⟨a, ?_, ?_⟩
  · have h1 : a * a + h.bar a * h.bar a ≠ 0 := by rw [ha, map_mul] at hne; exact hne
    simpa [sq] using h1
  · obtain ⟨r, hr⟩ := hdvd
    have hP : Polynomial.aeval (cG a (h.bar a))
        ((X : K[X]) ^ 3 + C τ * X ^ 2 + C (h.bar τ) * X + 1) = 0 := by
      have := cG_charpoly a (h.bar a) h2
      simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, map_one,
        Algebra.algebraMap_eq_smul_one]
      rw [hτb, ha]
      simpa [sq, smul_mul_assoc] using this
    have h3 := congrArg (Polynomial.aeval (cG a (h.bar a))) hr
    rw [map_mul, hP, zero_mul] at h3
    simp only [map_sub, map_pow, aeval_X, map_one] at h3
    exact sub_eq_zero.mp h3

end Core

section Main

variable {f : ℕ} {K : Type} [Field K]

@[expose] def invGL (T : Matrix (Fin 3) (Fin 3) K) (hT : T * T = 1) : GL (Fin 3) K := ⟨T, T, hT, hT⟩

theorem coe_invGL (T : Matrix (Fin 3) (Fin 3) K) (hT : T * T = 1) :
    ((invGL T hT : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = T := rfl

theorem invGL_mul_self (T : Matrix (Fin 3) (Fin 3) K) (hT : T * T = 1) :
    invGL T hT * invGL T hT = 1 := Units.ext (by rw [Units.val_mul, coe_invGL, hT]; rfl)

theorem exists_setup (hf : 2 ≤ f) (h : UnitaryFieldData 2 f K) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hord : orderOf (2 : ZMod ℓ) = 6 * f) :
    ∃ (a b : K) (H : GL (Fin 3) K), b = h.bar a ∧ h.bar b = a ∧ a ≠ 0 ∧ b ≠ 0 ∧
      a ^ 2 + b ^ 2 ≠ 0 ∧ cG a b ^ ℓ = 1 ∧
      ((H : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * cM a b * H = 1 := by
  obtain ⟨a, hne, hGℓ⟩ := exists_core h (by omega) hℓ hord
  obtain ⟨b, hb⟩ : ∃ b, b = h.bar a := ⟨_, rfl⟩
  rw [← hb] at hne hGℓ
  have hbb : h.bar b = a := by rw [hb]; exact h.bar_bar a
  have ha0 : a ≠ 0 := by
    intro h0
    apply hne
    rw [h0, map_zero] at hb
    rw [h0, hb]; ring
  have hb0 : b ≠ 0 := by
    intro h0
    apply ha0
    rw [← hbb, h0, map_zero]
  have hherm : ((cM a b).map h.bar)ᵀ = cM a b := by rw [hb]; exact cM_hermitian h a
  have hdetM : (cM a b).det ≠ 0 := by rw [det_cM]; exact hne
  obtain ⟨H, hH⟩ := exists_orthonormalizer h hherm hdetM
  exact ⟨a, b, H, hb, hbb, ha0, hb0, hne, hGℓ, hH⟩

theorem exists_three_involutions (hf : 2 ≤ f) (h : UnitaryFieldData 2 f K) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hord : orderOf (2 : ZMod ℓ) = 6 * f) :
    ∃ s₁ s₂ s₃ : unitarySU 2 f K 3, s₁ * s₁ = 1 ∧ s₁ ≠ 1 ∧ s₂ * s₂ = 1 ∧ s₂ ≠ 1 ∧
      s₃ * s₃ = 1 ∧ s₃ ≠ 1 ∧ orderOf (s₁ * s₂ * s₃) = ℓ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK2 : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨a, b, H, hb, hbb, ha0, hb0, hne, hGℓ, hH⟩ := exists_setup hf h hℓ hord
  have hg1 : invGL (cT1 a) (cT1_sq a h2) ∈ gramSU h (cM a b) := by
    refine mem_gramSU.mpr ⟨?_, ?_⟩
    · rw [coe_invGL, map_cT1, ← hb]; exact cT1_iso a b h2
    · rw [coe_invGL]; exact det_cT1 a
  have hg2 : invGL (cT2 a b) (cT2_sq a b h2) ∈ gramSU h (cM a b) := by
    refine mem_gramSU.mpr ⟨?_, ?_⟩
    · rw [coe_invGL, map_cT2, ← hb, hbb]; exact cT2_iso a b h2
    · rw [coe_invGL]; exact det_cT2 a b
  have hg3 : invGL (cT3 b) (cT3_sq b h2) ∈ gramSU h (cM a b) := by
    refine mem_gramSU.mpr ⟨?_, ?_⟩
    · rw [coe_invGL, map_cT3, hbb]; exact cT3_iso a b h2
    · rw [coe_invGL]; exact det_cT3 b
  let t1 : gramSU h (cM a b) := ⟨_, hg1⟩
  let t2 : gramSU h (cM a b) := ⟨_, hg2⟩
  let t3 : gramSU h (cM a b) := ⟨_, hg3⟩
  let E : gramSU h (cM a b) ≃* unitarySU 2 f K 3 :=
    (gramTransportSU h hH).symm.trans (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 3)).symm
  have ht1 : t1 * t1 = 1 := Subtype.ext (invGL_mul_self _ _)
  have ht2 : t2 * t2 = 1 := Subtype.ext (invGL_mul_self _ _)
  have ht3 : t3 * t3 = 1 := Subtype.ext (invGL_mul_self _ _)
  have ht1' : t1 ≠ 1 := by
    intro h0
    have := congrArg (fun x : gramSU h (cM a b) => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1) h0
    simp [t1, coe_invGL, cT1] at this
    exact ha0 this
  have ht2' : t2 ≠ 1 := by
    intro h0
    have := congrArg (fun x : gramSU h (cM a b) => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0) h0
    simp [t2, coe_invGL, cT2] at this
    exact hb0 this
  have ht3' : t3 ≠ 1 := by
    intro h0
    have := congrArg (fun x : gramSU h (cM a b) => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0) h0
    simp [t3, coe_invGL, cT3] at this
  have hGmat : (((t1 * t2 * t3 : gramSU h (cM a b)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      cG a b := by
    simp [t1, t2, t3, coe_invGL, cG]
  have hGpow : (t1 * t2 * t3) ^ ℓ = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hGmat, hGℓ]
    rfl
  have hG1 : t1 * t2 * t3 ≠ 1 := by
    intro h0
    have hmat : cG a b = 1 := by rw [← hGmat, h0]; rfl
    have := cG_charpoly a b h2
    rw [hmat] at this
    have h00 := congrFun (congrFun this 0) 0
    simp at h00
    apply hne
    linear_combination h00 - h2
  refine ⟨E t1, E t2, E t3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ht1, map_one]
  · exact fun h0 => ht1' (E.injective (by rw [h0, map_one]))
  · rw [← map_mul, ht2, map_one]
  · exact fun h0 => ht2' (E.injective (by rw [h0, map_one]))
  · rw [← map_mul, ht3, map_one]
  · exact fun h0 => ht3' (E.injective (by rw [h0, map_one]))
  · rw [← map_mul, ← map_mul, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hGpow hG1

end Main

end CFSG.QuasithinUnique.Setup.X5
