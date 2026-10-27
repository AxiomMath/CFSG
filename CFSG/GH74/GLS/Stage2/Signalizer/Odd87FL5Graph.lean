module

public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphTools

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.CatalogueBAlternatingIsometry

variable {K : Type*} [Field K]

@[expose] def signGroup (K : Type*) [Field K] : Subgroup Kˣ := (powMonoidHom 2 : Kˣ →* Kˣ).ker

theorem mem_signGroup {u : Kˣ} : u ∈ signGroup K ↔ u * u = 1 := by
  rw [signGroup, MonoidHom.mem_ker]
  simp [pow_two]

@[expose] noncomputable def signDiag (h : Fin 4 → ↥(signGroup K)) : Fin 5 → K := fun i =>
  if hi : (i : ℕ) < 4 then (((h ⟨i, hi⟩ : ↥(signGroup K)) : Kˣ) : K) else
    ∏ j, (((h j : ↥(signGroup K)) : Kˣ) : K)

theorem signDiag_mul (h h' : Fin 4 → ↥(signGroup K)) (i : Fin 5) :
    signDiag (h * h') i = signDiag h i * signDiag h' i := by
  unfold signDiag
  split_ifs with hi
  · simp
  · simp [Finset.prod_mul_distrib]

theorem unit_sq_eq_one {u : ↥(signGroup K)} : (((u : Kˣ) : K)) * ((u : Kˣ) : K) = 1 := by
  have h1 : (u : Kˣ) * (u : Kˣ) = 1 := mem_signGroup.1 u.2
  have := congrArg Units.val h1
  simpa [Units.val_mul] using this

theorem signDiag_sq (h : Fin 4 → ↥(signGroup K)) (i : Fin 5) : signDiag h i * signDiag h i = 1 := by
  unfold signDiag
  split_ifs with hi
  · exact unit_sq_eq_one
  · rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun j _ => unit_sq_eq_one

theorem signDiag_one : signDiag (1 : Fin 4 → ↥(signGroup K)) = fun _ => 1 := by
  funext i
  unfold signDiag
  split_ifs <;> simp

theorem prod_signDiag (h : Fin 4 → ↥(signGroup K)) : ∏ i, signDiag h i = 1 := by
  rw [Fin.prod_univ_castSucc]
  have h1 : ∀ i : Fin 4, signDiag h (Fin.castSucc i) = (((h i : ↥(signGroup K)) : Kˣ) : K) := fun i => by
    unfold signDiag
    simp
  have h2 : signDiag h (Fin.last 4) = ∏ j, (((h j : ↥(signGroup K)) : Kˣ) : K) := by
    unfold signDiag
    simp
  simp only [h1, h2]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun j _ => unit_sq_eq_one

@[expose] noncomputable def signGL : (Fin 4 → ↥(signGroup K)) →* GL (Fin 5) K where
  toFun h := ⟨diagonal (signDiag h), diagonal (signDiag h), by
    rw [diagonal_mul_diagonal]
    simp [signDiag_sq], by
    rw [diagonal_mul_diagonal]
    simp [signDiag_sq]⟩
  map_one' := by
    apply Units.ext
    simp [signDiag_one]
  map_mul' h h' := by
    apply Units.ext
    simp [diagonal_mul_diagonal, signDiag_mul]

theorem coe_signGL (h : Fin 4 → ↥(signGroup K)) :
    ((signGL h : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = diagonal (signDiag h) := rfl

theorem det_signGL (h : Fin 4 → ↥(signGroup K)) :
    ((signGL h : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det = 1 := by
  rw [coe_signGL, det_diagonal, prod_signDiag]

theorem eq_one_of_signGL_scalar {h : Fin 4 → ↥(signGroup K)} {c : K}
    (hmat : ((signGL h : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = scalar (Fin 5) c) : h = 1 := by
    have hd1 : ∀ i, signDiag h i = (c : K) := fun i => by
      have := congrFun (congrFun hmat i) i
      rw [coe_signGL] at this
      simpa [scalar_apply] using this
    have hu : ∀ k : Fin 4, (((h k : ↥(signGroup K)) : Kˣ) : K) = (c : K) := fun k => by
      have := hd1 (Fin.castSucc k)
      unfold signDiag at this
      simpa using this
    have hlast : ∏ j : Fin 4, (((h j : ↥(signGroup K)) : Kˣ) : K) = (c : K) := by
      have := hd1 (Fin.last 4)
      unfold signDiag at this
      simpa using this
    have hcc : (c : K) * (c : K) = 1 := by
      have := signDiag_sq h 0
      rwa [hd1] at this
    have hc1 : (c : K) = 1 := by
      have h4 : (c : K) ^ 4 = (c : K) := by
        calc (c : K) ^ 4 = ∏ j : Fin 4, (((h j : ↥(signGroup K)) : Kˣ) : K) := by
              simp only [hu, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          _ = (c : K) := hlast
      have h5 : (c : K) ^ 4 = 1 := by
        calc (c : K) ^ 4 = ((c : K) * (c : K)) * ((c : K) * (c : K)) := by ring
          _ = 1 := by rw [hcc]; ring
      rw [← h4, h5]
    funext k
    exact Subtype.ext (Units.ext (by simpa [hc1] using hu k))

theorem exists_elemAbelian_fixed_graph [Finite K] (hK : ringChar K ≠ 2) (A : GL (Fin 5) K)
    (hA : (A : Matrix (Fin 5) (Fin 5) K)ᵀ = A) :
    ∃ E : Subgroup (projectiveSL 5 K),
      (∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) ∧ (∀ e ∈ E, e * e = 1) ∧ 2 ^ 4 ≤ Nat.card ↥E ∧
      ∀ e ∈ E, (conjAut 5 K A * dualAut 5 K) e = e := by
  classical
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set R := ((A⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) with hR
  have hRt : Rᵀ = R := by
    have hAR : (A : Matrix (Fin 5) (Fin 5) K) * R = 1 := by
      rw [hR, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h1 : Rᵀ * (A : Matrix (Fin 5) (Fin 5) K)ᵀ = 1 := by
      rw [← transpose_mul, hR, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one]
    rw [hA] at h1
    calc Rᵀ = Rᵀ * ((A : Matrix (Fin 5) (Fin 5) K) * R) := by
          rw [hAR, Matrix.mul_one]
      _ = R := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hsymm : LinearMap.IsSymm (toBilin' R) := by
    refine LinearMap.isSymm_def.2 fun x y => ?_
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', dotProduct_mulVec, ← mulVec_transpose,
      hRt, dotProduct_comm]
    rfl
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis hsymm
  set b := v.reindex (finCongr (finrank_fin_fun K)) with hb
  have hbo : (toBilin' R).iIsOrtho b := fun i j hij => by
    change toBilin' R (b i) (b j) = 0
    rw [hb, Basis.reindex_apply, Basis.reindex_apply]
    exact hv (by simpa using hij)
  set d : Fin 5 → K := fun i => toBilin' R (b i) (b i) with hd
  have hG : LinearMap.BilinForm.toMatrix b (toBilin' R) = diagonal d := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, diagonal_apply]
    split_ifs with h
    · rw [h]
    · exact hbo h
  have hY : ∀ h : Fin 4 → ↥(signGroup K),
      ((signGL h : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)ᵀ *
        LinearMap.BilinForm.toMatrix b (toBilin' R) *
        ((signGL h : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      LinearMap.BilinForm.toMatrix b (toBilin' R) := fun h => by
    rw [hG, coe_signGL, diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    calc signDiag h i * d i * signDiag h i = (signDiag h i * signDiag h i) * d i := by ring
      _ = d i := by rw [signDiag_sq, one_mul]
  let ρ : (Fin 4 → ↥(signGroup K)) →* GL (Fin 5) K :=
    GeneralLinearGroup.toLin.symm.toMonoidHom.comp
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 5 → K)).symm.toMonoidHom.comp
        ((basisMatrixEquiv b).symm.toMonoidHom.comp signGL))
  have hρ : ∀ h, ((ρ h : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      LinearMap.toMatrix' ((basisMatrixEquiv b).symm (signGL h)).toLinearMap := fun h => rfl
  have hiso : ∀ h, (basisMatrixEquiv b).symm (signGL h) ∈
      isometryGroup (toBilin' R) := fun h => by
    rw [isometry_iff_matrix b, MulEquiv.apply_symm_apply]
    exact hY h
  have hstd : ∀ h, ((ρ h : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)ᵀ * R *
      (ρ h : Matrix (Fin 5) (Fin 5) K) = R := fun h => by
    have h1 := (isometry_iff_matrix (Pi.basisFun K (Fin 5)) (toBilin' R) _).1 (hiso h)
    rw [basisMatrixEquiv_val, LinearMap.toMatrix_eq_toMatrix',
      LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin'] at h1
    rw [hρ]
    exact h1
  have hdetρ : ∀ h, ((ρ h : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det = 1 := fun h => by
    rw [hρ, LinearMap.det_toMatrix']
    have h1 := congrArg Matrix.det (basisMatrixEquiv_val b ((basisMatrixEquiv b).symm (signGL h)))
    rw [MulEquiv.apply_symm_apply, LinearMap.det_toMatrix] at h1
    rw [← h1]
    exact det_signGL h
  let ρ' : (Fin 4 → ↥(signGroup K)) →* SpecialLinearGroup (Fin 5) K :=
    { toFun := fun h => ⟨ρ h, hdetρ h⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun h h' => Subtype.ext (by
        change ((ρ (h * h') : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
          (ρ h : Matrix (Fin 5) (Fin 5) K) * (ρ h' : Matrix (Fin 5) (Fin 5) K)
        rw [map_mul, Units.val_mul]) }
  set θ : (Fin 4 → ↥(signGroup K)) →* projectiveSL 5 K := (proj 5 K).comp ρ' with hθ
  refine ⟨θ.range, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨x, rfl⟩
    rw [← map_mul]
    have : x * x = 1 := by
      funext i
      have := mem_signGroup.1 (x i).2
      exact Subtype.ext (by simpa using this)
    rw [this, map_one]
  ·
    have hinj : Function.Injective θ := by
      rw [injective_iff_map_eq_one]
      intro h hh
      obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 hh)
      have hg : ((basisMatrixEquiv b).symm (signGL h)).toLinearMap = (c : K) • LinearMap.id := by
        apply LinearMap.toMatrix'.injective
        rw [← hρ h]
        rw [show ((ρ h : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
          ((ρ' h : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) from rfl, hc, map_smul,
          LinearMap.toMatrix'_id, scalar_apply, smul_one_eq_diagonal]
      have hmat : ((signGL h : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = scalar (Fin 5) (c : K) := by
        conv_lhs => rw [← MulEquiv.apply_symm_apply (basisMatrixEquiv b) (signGL h)]
        rw [basisMatrixEquiv_val, hg, map_smul, LinearMap.toMatrix_id, scalar_apply,
          smul_one_eq_diagonal]
      exact eq_one_of_signGL_scalar hmat
    have hcardΩ : 2 ≤ Nat.card ↥(signGroup K) := by
      have h1 : (1 : Kˣ) ≠ -1 := by
        intro h
        have := congrArg Units.val h
        simp only [Units.val_one, Units.val_neg] at this
        have h2' : (2 : K) = 0 := by linear_combination this
        exact h2 h2'
      have : 1 < Nat.card ↥(signGroup K) := by
        rw [Finite.one_lt_card_iff_nontrivial]
        refine ⟨⟨⟨1, (signGroup K).one_mem⟩, ⟨-1, mem_signGroup.2 (by simp)⟩, fun h => h1 ?_⟩⟩
        exact congrArg Subtype.val h
      omega
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_pi]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact Nat.pow_le_pow_left hcardΩ 4
  · rintro _ ⟨x, rfl⟩
    exact conjAut_dualAut_proj_of_transpose_mul_mul A ⟨_, hdetρ x⟩ (hstd x)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
