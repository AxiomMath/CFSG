module

public import CFSG.GH74.GLS.IVK.L2.FFNorm
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAut

public section

namespace CFSG.GH74.GLS.IVK

open Matrix CFSG.ABGLocalTools CFSG.GorensteinWalter

section SignMatrix

variable {F : Type} [Field F]

theorem exists_smul_one_of_commute_sl (M : Matrix (Fin 2) (Fin 2) F)
    (hM : ∀ b : SpecialLinearGroup (Fin 2) F,
      M * (b : Matrix (Fin 2) (Fin 2) F) = (b : Matrix (Fin 2) (Fin 2) F) * M) :
    ∃ μ : F, M = μ • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have h1 := hM ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have h2 := hM ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  rw [Matrix.eta_fin_two M] at h1 h2
  simp only [Matrix.mul_fin_two] at h1 h2
  have a1 := congrFun (congrFun h1 0) 0
  have a2 := congrFun (congrFun h1 0) 1
  have a3 := congrFun (congrFun h2 0) 0
  simp at a1 a2 a3
  have c11 : M 1 1 = M 0 0 := by linear_combination -a2
  refine ⟨M 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a1, a3, c11]


section GLNorm

theorem glMap_comp (σ τ : F ≃+* F) (G : GL (Fin 2) F) :
    GeneralLinearGroup.map (σ : F →+* F) (GeneralLinearGroup.map (τ : F →+* F) G) =
      GeneralLinearGroup.map ((σ * τ : F ≃+* F) : F →+* F) G := by
  apply Units.ext
  show ((G : Matrix (Fin 2) (Fin 2) F).map (τ : F → F)).map (σ : F → F) =
    (G : Matrix (Fin 2) (Fin 2) F).map ((σ * τ : F ≃+* F) : F → F)
  rw [Matrix.map_map]
  rfl

theorem glMap_one (G : GL (Fin 2) F) :
    GeneralLinearGroup.map (((1 : F ≃+* F)) : F →+* F) G = G := by
  apply Units.ext
  show (G : Matrix (Fin 2) (Fin 2) F).map ((1 : F ≃+* F) : F → F) = G
  ext i j
  rfl

theorem glNorm_succ_left (σ : F ≃+* F) (G : GL (Fin 2) F) (j : ℕ) :
    glNorm σ G (j + 1) = G * GeneralLinearGroup.map (σ : F →+* F) (glNorm σ G j) := by
  induction j with
  | zero =>
    rw [glNorm_succ, glNorm_zero, map_one, mul_one, one_mul, pow_zero, glMap_one]
  | succ j ih =>
    calc glNorm σ G (j + 1 + 1)
        = glNorm σ G (j + 1) * GeneralLinearGroup.map ((σ ^ (j + 1) : F ≃+* F) : F →+* F) G :=
          glNorm_succ σ G (j + 1)
      _ = (G * GeneralLinearGroup.map (σ : F →+* F) (glNorm σ G j)) *
            GeneralLinearGroup.map ((σ ^ (j + 1) : F ≃+* F) : F →+* F) G := by rw [ih]
      _ = G * GeneralLinearGroup.map (σ : F →+* F) (glNorm σ G (j + 1)) := by
          rw [glNorm_succ σ G j, map_mul, glMap_comp, mul_assoc, pow_succ']

theorem det_glNorm (σ : F ≃+* F) (G : GL (Fin 2) F) (j : ℕ) :
    ((glNorm σ G j : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      ∏ i ∈ Finset.range j, (σ ^ i) (G : Matrix (Fin 2) (Fin 2) F).det := by
  induction j with
  | zero => simp [glNorm_zero]
  | succ j ih =>
    rw [glNorm_succ, Units.val_mul, Matrix.det_mul, ih, Finset.prod_range_succ]
    congr 1
    show ((G : Matrix (Fin 2) (Fin 2) F).map ((σ ^ j : F ≃+* F) : F → F)).det = _
    exact (RingHom.map_det ((σ ^ j : F ≃+* F) : F →+* F) (G : Matrix (Fin 2) (Fin 2) F)).symm

theorem toGL_iterate (α : MulAut (SpecialLinearGroup (Fin 2) F)) (G : GL (Fin 2) F) (σ : F ≃+* F)
    (hα : ∀ b, SpecialLinearGroup.toGL (α b) =
      G * GeneralLinearGroup.map (σ : F →+* F) (SpecialLinearGroup.toGL b) * G⁻¹)
    (j : ℕ) (b : SpecialLinearGroup (Fin 2) F) :
    SpecialLinearGroup.toGL ((α ^ j) b) = glNorm σ G j *
      GeneralLinearGroup.map ((σ ^ j : F ≃+* F) : F →+* F) (SpecialLinearGroup.toGL b) *
        (glNorm σ G j)⁻¹ := by
  induction j with
  | zero =>
    rw [pow_zero, glNorm_zero, pow_zero, glMap_one]
    simp
  | succ j ih =>
    rw [pow_succ', MulAut.mul_apply, hα, ih, glNorm_succ_left, map_mul, map_mul, map_inv, glMap_comp, ← pow_succ']
    group

end GLNorm


section Sign

variable [Finite F]

theorem sign_lemma_matrix (h2 : (2 : F) ≠ 0) (α : MulAut (SpecialLinearGroup (Fin 2) F))
    (G : GL (Fin 2) F) (σ : F ≃+* F)
    (hα : ∀ b, SpecialLinearGroup.toGL (α b) =
      G * GeneralLinearGroup.map (σ : F →+* F) (SpecialLinearGroup.toGL b) * G⁻¹)
    (k : SpecialLinearGroup (Fin 2) F) (hk : α ^ orderOf σ = MulAut.conj k) (hαk : α k = k) :
    IsSquare ((G : Matrix (Fin 2) (Fin 2) F).det) := by
  have := finite_ringEquiv F
  set n := orderOf σ with hn
  set N := glNorm σ G n with hN
  have hσn : σ ^ n = 1 := pow_orderOf_eq_one σ
  have h1 : ∀ b : SpecialLinearGroup (Fin 2) F,
      SpecialLinearGroup.toGL ((α ^ n) b) = N * SpecialLinearGroup.toGL b * N⁻¹ := by
    intro b
    rw [toGL_iterate α G σ hα n b, hσn, glMap_one]
  have h1' : ∀ b : SpecialLinearGroup (Fin 2) F,
      N * SpecialLinearGroup.toGL b * N⁻¹ =
        SpecialLinearGroup.toGL k * SpecialLinearGroup.toGL b * (SpecialLinearGroup.toGL k)⁻¹ := by
    intro b
    rw [← h1 b, hk, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hcomm : ∀ b : SpecialLinearGroup (Fin 2) F,
      (((SpecialLinearGroup.toGL k)⁻¹ * N : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          (b : Matrix (Fin 2) (Fin 2) F) =
        (b : Matrix (Fin 2) (Fin 2) F) *
          (((SpecialLinearGroup.toGL k)⁻¹ * N : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    intro b
    have e1 := h1' b
    have e2 : (SpecialLinearGroup.toGL k)⁻¹ * N * SpecialLinearGroup.toGL b =
        SpecialLinearGroup.toGL b * ((SpecialLinearGroup.toGL k)⁻¹ * N) := by
      have : (SpecialLinearGroup.toGL k)⁻¹ * (N * SpecialLinearGroup.toGL b * N⁻¹) * N =
          SpecialLinearGroup.toGL b * ((SpecialLinearGroup.toGL k)⁻¹ * N) := by
        rw [e1]; group
      rw [← this]; group
    exact congrArg (fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F)) e2
  obtain ⟨μ, hμ⟩ := exists_smul_one_of_commute_sl _ hcomm
  set k' : GL (Fin 2) F := SpecialLinearGroup.toGL k with hk'
  have hk'm : (k' : Matrix (Fin 2) (Fin 2) F) = (k : Matrix (Fin 2) (Fin 2) F) := rfl
  have hNmat : (N : Matrix (Fin 2) (Fin 2) F) = μ • (k' : Matrix (Fin 2) (Fin 2) F) := by
    have : N = k' * (k'⁻¹ * N) := by group
    rw [this, Units.val_mul, hμ, Matrix.mul_smul, Matrix.mul_one]
  have hdetN : (N : Matrix (Fin 2) (Fin 2) F).det = μ ^ 2 := by
    rw [hNmat, Matrix.det_smul, hk'm, k.det_coe, Fintype.card_fin, mul_one]
  have hdet : μ ^ 2 = ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) (G : Matrix (Fin 2) (Fin 2) F).det := by
    rw [← hdetN, hN, hn, det_glNorm]
  have hN5 : G * GeneralLinearGroup.map (σ : F →+* F) N = N * G := by
    have e1 := glNorm_succ_left σ G n
    have e2 := glNorm_succ σ G n
    rw [e1, hσn, glMap_one] at e2
    exact e2
  have hk6 : k' * G = G * GeneralLinearGroup.map (σ : F →+* F) k' := by
    have e := hα k
    rw [hαk] at e
    calc k' * G = G * GeneralLinearGroup.map (σ : F →+* F) k' * G⁻¹ * G := by rw [← e]
      _ = G * GeneralLinearGroup.map (σ : F →+* F) k' := by group
  have hN5m : (G : Matrix (Fin 2) (Fin 2) F) * (N : Matrix (Fin 2) (Fin 2) F).map σ =
      (N : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) :=
    congrArg (fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F)) hN5
  have hk6m : (k' : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) =
      (G : Matrix (Fin 2) (Fin 2) F) * (k' : Matrix (Fin 2) (Fin 2) F).map σ :=
    congrArg (fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F)) hk6
  have hmapsmul : (N : Matrix (Fin 2) (Fin 2) F).map σ =
      σ μ • (k' : Matrix (Fin 2) (Fin 2) F).map σ := by
    rw [hNmat]
    ext i j
    simp [Matrix.map_apply]
  have hP : σ μ • ((k' : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F)) =
      μ • ((k' : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F)) := by
    calc σ μ • ((k' : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F))
        = σ μ • ((G : Matrix (Fin 2) (Fin 2) F) * (k' : Matrix (Fin 2) (Fin 2) F).map σ) := by
          rw [hk6m]
      _ = (G : Matrix (Fin 2) (Fin 2) F) * (σ μ • (k' : Matrix (Fin 2) (Fin 2) F).map σ) :=
          (Matrix.mul_smul _ _ _).symm
      _ = (μ • (k' : Matrix (Fin 2) (Fin 2) F)) * (G : Matrix (Fin 2) (Fin 2) F) := by
          rw [← hmapsmul, ← hNmat]; exact hN5m
      _ = μ • ((k' : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F)) :=
          Matrix.smul_mul _ _ _
  have hPP : ((k' * G : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (((k' * G)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hσμ : σ μ = μ := by
    have e := congrArg (fun A : Matrix (Fin 2) (Fin 2) F =>
      A * (((k' * G)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) hP
    simp only [Units.val_mul] at e hPP
    rw [Matrix.smul_mul, Matrix.smul_mul, hPP] at e
    have e00 := congrFun (congrFun e 0) 0
    simpa using e00
  have hd : (G : Matrix (Fin 2) (Fin 2) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 G.isUnit).ne_zero
  exact isSquare_of_prod_fixed_sq h2 σ hd hσμ hdet

end Sign


section Descr

variable [Finite F]

noncomputable def slSemilinear (G : GL (Fin 2) F) (σ : F ≃+* F) :
    SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) F where
  toFun b := ⟨(G : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F).map σ *
      ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), by
    rw [Matrix.det_mul, Matrix.det_mul]
    have h1 : (G : Matrix (Fin 2) (Fin 2) F).det * ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det
        = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    have h2 : ((b : Matrix (Fin 2) (Fin 2) F).map σ).det = 1 := by
      have := RingHom.map_det (σ : F →+* F) (b : Matrix (Fin 2) (Fin 2) F)
      rw [b.det_coe, map_one] at this
      exact this.symm
    rw [h2, mul_one, h1]⟩
  map_one' := by
    apply Subtype.ext
    show (G : Matrix (Fin 2) (Fin 2) F) * (1 : Matrix (Fin 2) (Fin 2) F).map σ *
        ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
    rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.mul_one, ← Units.val_mul, mul_inv_cancel,
      Units.val_one]
  map_mul' a b := by
    apply Subtype.ext
    show (G : Matrix (Fin 2) (Fin 2) F) * ((a : Matrix (Fin 2) (Fin 2) F) *
          (b : Matrix (Fin 2) (Fin 2) F)).map σ * ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((G : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F).map σ *
          ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
        ((G : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F).map σ *
          ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
    have hGG : ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [Matrix.map_mul]
    calc (G : Matrix (Fin 2) (Fin 2) F) * ((a : Matrix (Fin 2) (Fin 2) F).map σ *
            (b : Matrix (Fin 2) (Fin 2) F).map σ) * ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = (G : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F).map σ * 1 *
            (b : Matrix (Fin 2) (Fin 2) F).map σ * ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
          simp [Matrix.mul_assoc]
      _ = _ := by rw [← hGG]; simp only [Matrix.mul_assoc]


theorem eq_of_smul_eq (hF : ringChar F ≠ 2)
    (α β : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) F)
    (h : ∀ b, ∃ u : F, (α b : Matrix (Fin 2) (Fin 2) F) = u • (β b : Matrix (Fin 2) (Fin 2) F)) :
    α = β := by
  have hr : (ringChar F).Prime := ringChar_prime
  apply MonoidHom.eq_of_eqOn_dense
    SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
  rintro _ ⟨t, rfl⟩
  set x := t.toSpecialLinearGroup with hx
  have hxr : x ^ ringChar F = 1 := CFSG.LieType.CentralExt.toSpecialLinearGroup_pow_ringChar t
  obtain ⟨u, hu⟩ := h x
  have hdet : u ^ 2 = 1 := by
    have h1 := congrArg Matrix.det hu
    rw [(α x).det_coe, Matrix.det_smul, (β x).det_coe, Fintype.card_fin] at h1
    simpa using h1.symm
  have hpow : u ^ (ringChar F) = 1 := by
    have h1 : (((α x) ^ ringChar F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← map_pow, hxr, map_one]; rfl
    have h2 : (((β x) ^ ringChar F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← map_pow, hxr, map_one]; rfl
    rw [Matrix.SpecialLinearGroup.coe_pow, hu, smul_pow] at h1
    rw [Matrix.SpecialLinearGroup.coe_pow] at h2
    rw [h2] at h1
    have h3 := congrFun (congrFun h1 0) 0
    simpa using h3
  have hodd : Odd (ringChar F) := hr.odd_of_ne_two hF
  obtain ⟨m, hm⟩ := hodd
  have hu1 : u = 1 := by
    have : u ^ (2 * m + 1) = u := by rw [pow_succ, pow_mul, hdet, one_pow, one_mul]
    rw [← this, ← hm, hpow]
  rw [hu1, one_smul] at hu
  exact Subtype.ext hu

theorem semilinear_of_pGammaL2 (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (α : MulAut (SpecialLinearGroup (Fin 2) F)) (γ : PGammaL2 F)
    (hγ : pGammaL2ToMulAutPSL2 F (isOddPrimePower_card_of_odd hodd) h3 γ = psl2MulAutOf α)
    (G : GL (Fin 2) F) (hG : ProjGenLinGroup.mk G = γ.left) (b : SpecialLinearGroup (Fin 2) F) :
    SpecialLinearGroup.toGL (α b) =
      G * GeneralLinearGroup.map (γ.right : F →+* F) (SpecialLinearGroup.toGL b) * G⁻¹ := by
  have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_odd_card hodd
  have hK := isOddPrimePower_card_of_odd hodd
  have hαβ : α.toMonoidHom = slSemilinear G γ.right := by
    apply eq_of_smul_eq hF2
    intro b
    obtain ⟨u, -, hu⟩ := coe_mulAut_eq_smul_conj hK h3 α γ hγ G hG b
    exact ⟨u, hu⟩
  apply Units.ext
  have := congrArg (fun φ : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) F =>
    ((φ b : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) hαβ
  exact this

theorem exists_semilinear_of_mulAut (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (α : MulAut (SpecialLinearGroup (Fin 2) F)) :
    ∃ (G : GL (Fin 2) F) (σ : F ≃+* F), ∀ b, SpecialLinearGroup.toGL (α b) =
      G * GeneralLinearGroup.map (σ : F →+* F) (SpecialLinearGroup.toGL b) * G⁻¹ := by
  have hK := isOddPrimePower_card_of_odd hodd
  obtain ⟨f, -, hKcard⟩ := card_eq_ringChar_pow (F := F)
  have : Fact (ringChar F).Prime := ⟨ringChar_prime⟩
  obtain ⟨γ, hγ⟩ := pGammaL2ToMulAutPSL2_surjective F hKcard hK h3 (psl2MulAutOf α)
  obtain ⟨G, hG⟩ := Matrix.ProjGenLinGroup.mk_surjective γ.left
  exact ⟨G, γ.right, semilinear_of_pGammaL2 hodd h3 α γ hγ G hG⟩

end Descr

end SignMatrix

end CFSG.GH74.GLS.IVK
