module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_5_2L2Field

public section

open scoped MatrixGroups

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.Open CFSG.Quasithin.H11 CFSG.HardMathSupport.Solomon.LocalBalance

variable {F : Type} [Field F] [CharP F 2]

theorem l2op_exists_mul_map_eq [Finite F] (σ : F ≃+* F) (hσ : orderOf σ = 3) (g : SL(2, F))
    (hg : g * l2opFieldAutHom σ g * l2opFieldAutHom (σ ^ 2) g = 1) :
    ∃ h : SL(2, F), g * l2opFieldAutHom σ h = h := by
  classical
  set A : GL (Fin 2) F := Matrix.SpecialLinearGroup.toGL g with hA
  have hnorm : CFSG.ABGLocalTools.glNorm σ A 3 =
      Matrix.SpecialLinearGroup.toGL (g * l2opFieldAutHom σ g * l2opFieldAutHom (σ ^ 2) g) := by
    apply Units.ext
    simp only [CFSG.ABGLocalTools.glNorm_succ, CFSG.ABGLocalTools.glNorm_zero, one_mul,
      Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_two, l2opFieldAutHom_apply_apply, hA, sq,
      MulAut.mul_apply]
  have hc : ((CFSG.ABGLocalTools.glNorm σ A (orderOf σ) : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) (1 : F) := by
    rw [hσ, hnorm, hg, map_one, Units.val_one, map_one]
  obtain ⟨H, d, hHd⟩ := CFSG.RankThree.LinearTwo.exists_mul_map_eq_smul σ A hc
  have hHd' : ∀ i j, g i 0 * σ ((H : Matrix (Fin 2) (Fin 2) F) 0 j) +
      g i 1 * σ ((H : Matrix (Fin 2) (Fin 2) F) 1 j) =
        (d : F) * (H : Matrix (Fin 2) (Fin 2) F) i j := by
    intro i j
    have := hHd i j
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hA] using this
  set δ := (H : Matrix (Fin 2) (Fin 2) F).det with hδ
  have hδ0 : δ ≠ 0 := by
    rw [hδ, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hσδ : σ δ = (d : F) ^ 2 * δ := by
    have hM : (g : Matrix (Fin 2) (Fin 2) F) *
        (σ : F →+* F).mapMatrix (H : Matrix (Fin 2) (Fin 2) F) =
          (d : F) • (H : Matrix (Fin 2) (Fin 2) F) := by
      ext i j
      rw [Matrix.smul_apply, smul_eq_mul, ← hHd' i j]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    have := congrArg Matrix.det hM
    rw [Matrix.det_mul, ← RingHom.map_det, Matrix.det_smul, Fintype.card_fin] at this
    have hg1 : (g : Matrix (Fin 2) (Fin 2) F).det = 1 := g.2
    rw [hg1, one_mul] at this
    exact this
  obtain ⟨e, he⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) δ
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hδ0 (by rw [he, mul_zero])
  have hσe : σ e = (d : F) * e := by
    apply CharTwo.sq_injective
    change σ e ^ 2 = ((d : F) * e) ^ 2
    rw [← map_pow, sq, ← he, hσδ, he]
    ring
  refine ⟨⟨e⁻¹ • (H : Matrix (Fin 2) (Fin 2) F), ?_⟩, ?_⟩
  · rw [Matrix.det_smul, Fintype.card_fin, ← hδ, he]
    field_simp
  · ext i j
    have hd0 : (d : F) ≠ 0 := d.ne_zero
    have key := hHd' i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    change g i 0 * σ (e⁻¹ * (H : Matrix (Fin 2) (Fin 2) F) 0 j) +
      g i 1 * σ (e⁻¹ * (H : Matrix (Fin 2) (Fin 2) F) 1 j) =
        e⁻¹ * (H : Matrix (Fin 2) (Fin 2) F) i j
    rw [map_mul, map_mul, map_inv₀, hσe]
    calc _ = ((d : F) * e)⁻¹ * (g i 0 * σ ((H : Matrix (Fin 2) (Fin 2) F) 0 j) +
          g i 1 * σ ((H : Matrix (Fin 2) (Fin 2) F) 1 j)) := by ring
      _ = ((d : F) * e)⁻¹ * ((d : F) * (H : Matrix (Fin 2) (Fin 2) F) i j) := by rw [key]
      _ = _ := by field_simp

omit [CharP F 2] in
theorem l2op_conj_mul_fieldAut (σ : F ≃+* F) {g h : SL(2, F)}
    (hgh : g * l2opFieldAutHom σ h = h) :
    MulAut.conj g * l2opFieldAutHom σ = MulAut.conj h * l2opFieldAutHom σ * (MulAut.conj h)⁻¹ := by
  have hg : g = h * (l2opFieldAutHom σ h)⁻¹ := eq_mul_inv_of_mul_eq hgh
  subst hg
  ext x : 1
  simp [MulAut.conj_apply, map_mul, map_inv, mul_assoc]

theorem l2op_conj_mul_pow_three {K : Type*} [Group K] (s : MulAut K) (g : K) :
    (MulAut.conj g * s) ^ 3 = MulAut.conj (g * s g * s (s g)) * s ^ 3 := by
  ext x : 1
  simp [pow_succ, MulAut.conj_apply, map_mul, map_inv, mul_assoc]

theorem l2op_exists_conj_fieldAut [Finite F] (f : MulAut SL(2, F)) (hf3 : f ^ 3 = 1)
    (hf : f ∉ innerAut SL(2, F)) :
    ∃ (σ : F ≃+* F) (c : MulAut SL(2, F)), orderOf σ = 3 ∧ f = c * l2opFieldAutHom σ * c⁻¹ := by
  obtain ⟨σ, g, hfg⟩ := exists_aut_formula f
  have hf' : f = MulAut.conj g * l2opFieldAutHom σ := by
    ext x : 1
    rw [hfg x]
    rfl
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    apply hf
    refine ⟨g, ?_⟩
    rw [hf', map_one, mul_one]
  have hcube := l2op_conj_mul_pow_three (l2opFieldAutHom σ) g
  rw [← hf', hf3, ← map_pow] at hcube
  have hid : ∀ γ, (g * l2opFieldAutHom σ g * l2opFieldAutHom σ (l2opFieldAutHom σ g)) *
      Matrix.SpecialLinearGroup.map (σ ^ 3).toRingHom γ *
      (g * l2opFieldAutHom σ g * l2opFieldAutHom σ (l2opFieldAutHom σ g))⁻¹ = γ := by
    intro γ
    have := congrArg (fun φ : MulAut SL(2, F) => φ γ) hcube
    simp only [MulAut.one_apply, MulAut.mul_apply, MulAut.conj_apply] at this
    exact this.symm
  obtain ⟨hσ3, hz⟩ := eq_one_of_aut_formula (σ ^ 3) _ hid
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hz' : g * l2opFieldAutHom σ g * l2opFieldAutHom (σ ^ 2) g = 1 := by
    rw [map_pow, pow_two, MulAut.mul_apply]
    exact hz
  obtain ⟨h, hh⟩ := l2op_exists_mul_map_eq σ hord g hz'
  exact ⟨σ, MulAut.conj h, hord, hf'.trans (l2op_conj_mul_fieldAut σ hh)⟩

end CFSG.HardMathSupport.Solomon.Coordinator
