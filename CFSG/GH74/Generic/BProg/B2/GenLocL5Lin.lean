module

public import CFSG.GH74.Generic.BProg.B2.GenLocL5Sign
public import CFSG.GH74.Generic.BProg.B2.GenLocL5Gen

public section

namespace CFSG.GH74.Generic.BProg.B2.GenLocL5Lin

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OddHigherLinear
  CFSG.LocalAnalysis.ComponentInitial.FourGroupOddBilinear CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification

variable {K : Type} [Field K]

theorem conjAut_scalar {n : ℕ} (u : Kˣ) :
    LinearFlag.conjAut n K (Matrix.GeneralLinearGroup.scalar (Fin n) u) = 1 := by
  have hc : Matrix.GeneralLinearGroup.scalar (Fin n) u ∈ Subgroup.center (GL (Fin n) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u, rfl⟩
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  rw [conjAut_proj, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  have hcomm := Subgroup.mem_center_iff.mp hc (Matrix.SpecialLinearGroup.toGL g)
  rw [coe_slConjugation, ← Matrix.SpecialLinearGroup.coe_GL_coe_matrix g,
    ← Units.val_mul, ← Units.val_mul, ← hcomm, mul_inv_cancel_right]

theorem conj_proj_eq_conjAut {n : ℕ} (g : SpecialLinearGroup (Fin n) K) :
    MulAut.conj (LinearFlag.proj n K g) = LinearFlag.conjAut n K (SpecialLinearGroup.toGL g) := by
  ext x
  obtain ⟨h, rfl⟩ := proj_surjective n K x
  rw [MulAut.conj_apply, conjAut_proj, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [CatalogueBHigherLinearAction.toGL_slConjugation, map_mul, map_mul, map_inv]


theorem conjAut_mem_inner_of_sq [Finite K] {n : ℕ} (hn : Odd n) (hn3 : 3 ≤ n) (A : GL (Fin n) K)
    (hA : LinearFlag.conjAut n K A * LinearFlag.conjAut n K A = 1) :
    LinearFlag.conjAut n K A ∈
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  have h1 : LinearFlag.conjAut n K (A * A) * LinearFlag.fieldAut n K 1 = 1 := by
    rw [map_one, mul_one, map_mul]; exact hA
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn3 (A * A) 1 h1
  obtain ⟨m, rfl⟩ := hn
  set d : Kˣ := Matrix.GeneralLinearGroup.det A with hd
  have hdc : d ^ 2 = c ^ (2 * m + 1) := by
    have h2 := congrArg (Matrix.GeneralLinearGroup.det) hc
    rw [map_mul, ← pow_two] at h2
    rw [hd, ← h2]
    ext
    simp
  set e : Kˣ := d * (c ^ m)⁻¹ with he
  have hen : e ^ (2 * m + 1) = d := by
    have h3 : d ^ (2 * m + 1) = d * (c ^ (2 * m + 1)) ^ m := by
      rw [pow_succ, pow_mul, hdc, mul_comm]
    have h4 : (c ^ m) ^ (2 * m + 1) = (c ^ (2 * m + 1)) ^ m := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    rw [he, mul_pow, inv_pow, h3, h4, mul_inv_cancel_right]
  set B : GL (Fin (2 * m + 1)) K :=
    A * Matrix.GeneralLinearGroup.scalar (Fin (2 * m + 1)) e⁻¹ with hB
  have hdet : Matrix.GeneralLinearGroup.det B = 1 := by
    have hs : Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.scalar (Fin (2 * m + 1)) e⁻¹ : GL (Fin (2 * m + 1)) K) =
        e⁻¹ ^ (2 * m + 1) := by
      ext
      simp
    rw [hB, map_mul, hs, inv_pow, hen, mul_inv_cancel]
  have hdet' : (B : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K).det = 1 := by
    have := congrArg Units.val hdet
    simpa using this
  set g : SpecialLinearGroup (Fin (2 * m + 1)) K :=
    ⟨(B : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K), hdet'⟩ with hg
  have hBA : A =
      SpecialLinearGroup.toGL g * Matrix.GeneralLinearGroup.scalar (Fin (2 * m + 1)) e := by
    have h1 : SpecialLinearGroup.toGL g = B := by
      ext
      rfl
    rw [h1, hB, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  refine ⟨LinearFlag.proj (2 * m + 1) K g, ?_⟩
  rw [conj_proj_eq_conjAut, hBA, map_mul, conjAut_scalar, mul_one]


theorem exists_fixed_E16 [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (β : MulAut (projectiveSL 5 K)) (hβ : β * β = 1)
    (hβi : β ∉ (MulAut.conj : projectiveSL 5 K →* MulAut (projectiveSL 5 K)).range) :
    ∃ V : Subgroup (projectiveSL 5 K), (∀ x ∈ V, β x = x) ∧ CFSG.IsElementaryAbelian 2 ↥V ∧
      Nat.card ↥V = 16 := by
  classical
  have hn : 3 ≤ 5 := by norm_num
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.odd_of_ne_two hp2).pow
  have hK2 : ringChar K ≠ 2 := CatalogueBHigherLinearInner.ringChar_ne_two_of_odd_card K hodd
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hea : CFSG.IsElementaryAbelian 2 ↥(GenLocL5Sign.signGroup 5 K) :=
    GenLocL5Sign.isEA_signGroup 5
  have hV₀f : ∀ σ : K ≃+* K, ∀ v ∈ GenLocL5Sign.signGroup 5 K, LinearFlag.fieldAut 5 K σ v = v := by
    rintro σ _ ⟨S, hS, rfl⟩
    exact fieldAut_proj_signSL σ S hS
  have hV₀d : ∀ v ∈ GenLocL5Sign.signGroup 5 K, LinearFlag.dualAut 5 K v = v := by
    rintro _ ⟨S, hS, rfl⟩
    exact dualAut_proj_signSL S hS
  have hconj : ∀ (H : GL (Fin 5) K) (γ : MulAut (projectiveSL 5 K)),
      (∀ v ∈ GenLocL5Sign.signGroup 5 K, γ v = v) →
      β = LinearFlag.conjAut 5 K H * γ * (LinearFlag.conjAut 5 K H)⁻¹ →
      ∃ V : Subgroup (projectiveSL 5 K), (∀ x ∈ V, β x = x) ∧ CFSG.IsElementaryAbelian 2 ↥V ∧
        Nat.card ↥V = 16 := by
    intro H γ hγ hβH
    refine ⟨(GenLocL5Sign.signGroup 5 K).map (LinearFlag.conjAut 5 K H).toMonoidHom, ?_,
      CFSG.IsElementaryAbelian.map _, ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      change β (LinearFlag.conjAut 5 K H v) = LinearFlag.conjAut 5 K H v
      rw [hβH, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply,
        hγ v hv]
    · rw [Subgroup.card_map_of_injective (MulEquiv.injective _),
        GenLocL5Sign.card_signGroup rfl h2]
  obtain ⟨-, hform⟩ := automorphism_generation (K := K) (n := 5) hn
  obtain ⟨A, σ, ε, hε, rfl⟩ := hform β
  have hβ2 : (LinearFlag.conjAut 5 K A * LinearFlag.fieldAut 5 K σ *
      LinearFlag.dualAut 5 K ^ ε) ^ 2 = 1 := by
    rw [pow_two]; exact hβ
  interval_cases ε
  ·
    rw [pow_zero, mul_one] at hβ2 hβ hβi ⊢
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hβ hβi
      exact absurd (conjAut_mem_inner_of_sq (by decide) hn A hβ) hβi
    · obtain ⟨H, hH⟩ := OddHigherLinear.field_involution_conjugacy hp hp2 hf hK hn A σ hσ hβ2
      exact hconj H (LinearFlag.fieldAut 5 K σ) (hV₀f σ) hH
  ·
    rw [pow_one] at hβ2 hβ hβi ⊢
    by_cases hσ : σ = 1
    · subst hσ
      have hAt : (A : Matrix (Fin 5) (Fin 5) K)ᵀ = A := by
        rcases transpose_eq_or_eq_neg_of_sq hn A hβ2 with h | h
        · exact h
        · exfalso
          have h1 := congrArg Matrix.det h
          rw [det_transpose, det_neg, Fintype.card_fin] at h1
          have hdet : (A : Matrix (Fin 5) (Fin 5) K).det ≠ 0 :=
            ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).ne_zero
          apply hdet
          have h3 : (2 : K) * (A : Matrix (Fin 5) (Fin 5) K).det = 0 := by
            norm_num at h1
            linear_combination h1
          exact (mul_eq_zero.1 h3).resolve_left h2
      set R : GL (Fin 5) K := A⁻¹ with hRdef
      have hAR : (A : Matrix (Fin 5) (Fin 5) K) * R = 1 := by
        rw [hRdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hRAt : (R : Matrix (Fin 5) (Fin 5) K)ᵀ * (A : Matrix (Fin 5) (Fin 5) K)ᵀ = 1 := by
        rw [← transpose_mul, hAR, transpose_one]
      have hR : (R : Matrix (Fin 5) (Fin 5) K)ᵀ = R := by
        calc (R : Matrix (Fin 5) (Fin 5) K)ᵀ
            = (R : Matrix (Fin 5) (Fin 5) K)ᵀ * (A * R) := by rw [hAR, Matrix.mul_one]
          _ = ((R : Matrix (Fin 5) (Fin 5) K)ᵀ * (A : Matrix (Fin 5) (Fin 5) K)ᵀ) * R := by
              rw [hAt, Matrix.mul_assoc]
          _ = R := by rw [hRAt, Matrix.one_mul]
      obtain ⟨V, hVle, hVab, hVcard⟩ := GenLocL5Sign.exists_E16_isometry rfl hK2 R hR
      refine ⟨V, fun x hx => ?_, hVab, hVcard⟩
      obtain ⟨g, hg, rfl⟩ := hVle hx
      change (LinearFlag.conjAut 5 K A * LinearFlag.fieldAut 5 K 1 * LinearFlag.dualAut 5 K)
        (LinearFlag.proj 5 K g) = LinearFlag.proj 5 K g
      rw [map_one, mul_one, MulAut.mul_apply, dualAut_proj, conjAut_proj]
      congr 1
      refine Subtype.ext ?_
      rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_transpose]
      have hgI : (g : Matrix (Fin 5) (Fin 5) K)ᵀ * R * g = R := mem_isometrySL.1 hg
      have hgg : (g : Matrix (Fin 5) (Fin 5) K) *
          ((g⁻¹ : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
      calc (A : Matrix (Fin 5) (Fin 5) K) *
            ((g⁻¹ : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)ᵀ *
            ((A⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
          = A * (((g⁻¹ : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)ᵀ *
              ((g : Matrix (Fin 5) (Fin 5) K)ᵀ * R * g)) := by
            rw [hgI, Matrix.mul_assoc]
        _ = A * (((g : Matrix (Fin 5) (Fin 5) K) *
              ((g⁻¹ : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))ᵀ * R * g) := by
            rw [transpose_mul]
            simp only [Matrix.mul_assoc]
        _ = (A * R) * g := by rw [hgg, transpose_one, Matrix.one_mul, Matrix.mul_assoc]
        _ = g := by rw [hAR, Matrix.one_mul]
    · obtain ⟨-, -, H, hH⟩ := odd_linear_graph_field_involution_conjugacy hp hf hK hn A σ hσ hβ2
      exact hconj H (LinearFlag.fieldAut 5 K σ * LinearFlag.dualAut 5 K)
        (fun v hv => by rw [MulAut.mul_apply, hV₀d v hv, hV₀f σ v hv]) hH


theorem out16_of_stated {J : Type} [Group J] {p f : ℕ} (hp2 : p ≠ 2)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel J .PSL 5 p f) : GenLocL5Gen.Out16 J := by
  obtain ⟨⟨hprime, hf, -⟩, F, _, _, hF, ⟨e⟩⟩ := h
  let ψ : J ≃* projectiveSL 5 F :=
    e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 5 F).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 5 F))
  refine GenLocL5Gen.Out16.of_mulEquiv ψ.symm fun β hβ hβi => ?_
  exact exists_fixed_E16 hprime hp2 hf hF β hβ hβi

end CFSG.GH74.Generic.BProg.B2.GenLocL5Lin
