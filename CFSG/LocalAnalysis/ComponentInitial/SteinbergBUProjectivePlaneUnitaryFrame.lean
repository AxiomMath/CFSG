module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix CFSG.ClassicalGroups.UnitaryFlag

variable {r f : ℕ} {K : Type*} [Field K] (h : UnitaryFieldData r f K)

section ConjTranspose

variable {ι : Type*}

theorem conjT_diagonal [DecidableEq ι] (d : ι → K) :
    ((diagonal d).map h.bar)ᵀ = diagonal fun i => h.bar (d i) := by
  rw [diagonal_map (map_zero _), diagonal_transpose]

theorem conjT_conjT (M : Matrix ι ι K) : (((M.map h.bar)ᵀ).map h.bar)ᵀ = M := by
  ext i j
  simp [h.bar_bar]

theorem conjT_mul [Fintype ι] (M N : Matrix ι ι K) :
    ((M * N).map h.bar)ᵀ = (N.map h.bar)ᵀ * (M.map h.bar)ᵀ := by
  rw [Matrix.map_mul, transpose_mul]

theorem conjT_one [DecidableEq ι] : ((1 : Matrix ι ι K).map h.bar)ᵀ = 1 := by
  rw [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one]

variable [Fintype ι] [DecidableEq ι]

theorem isometry_conj_diagGL {Q : GL ι K} {G : Matrix ι ι K}
    (hQ : ((Q : Matrix ι ι K).map h.bar)ᵀ * G * Q = 1) {x : ι → Kˣ}
    (hx : ∀ i, h.norm (x i : K) = 1) :
    (((Q * TauCeti.diagGL x * Q⁻¹ : GL ι K) : Matrix ι ι K).map h.bar)ᵀ * G *
      ((Q * TauCeti.diagGL x * Q⁻¹ : GL ι K) : Matrix ι ι K) = G := by
  set Qm := (Q : Matrix ι ι K)
  set Qi := ((Q⁻¹ : GL ι K) : Matrix ι ι K)
  have hQQ : Qm * Qi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hG : G = (Qi.map h.bar)ᵀ * Qi := by
    have h1 := conjTranspose_mul_mul h G Qm Qi
    rw [hQ, hQQ, conjT_one] at h1
    simpa only [Matrix.one_mul, Matrix.mul_one] using h1
  have hD : ((diagonal fun i => (x i : K)).map h.bar)ᵀ * (diagonal fun i => (x i : K)) = 1 := by
    rw [conjT_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [mul_comm]
    exact hx i
  rw [Units.val_mul, Units.val_mul, TauCeti.diagGL_coe, conjTranspose_mul_mul,
    conjTranspose_mul_mul, hQ, Matrix.mul_one, hD, Matrix.mul_one, ← hG]

end ConjTranspose

theorem norm_pow (ζ : K) (k : ℕ) : h.norm (ζ ^ k) = h.norm ζ ^ k := by
  simp only [UnitaryFieldData.norm, map_pow, mul_pow]

theorem bar_eq_inv_of_norm {ζ : K} (hζ : h.norm ζ = 1) : h.bar ζ = ζ⁻¹ :=
  (eq_inv_of_mul_eq_one_right hζ)

theorem norm_eq_one_of_pow_eq_one {p : ℕ} [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hN : h.norm ζ = 1) {x : K} (hx : x ^ p = 1) : h.norm x = 1 := by
  obtain ⟨k, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
  rw [norm_pow, hN, one_pow]

theorem exists_orthonormal_frame [Finite K] {p : ℕ} [NeZero p] {G : Matrix (Fin p) (Fin p) K}
    (hGh : (G.map h.bar)ᵀ = G) (hGu : IsUnit G) {X : Matrix (Fin p) (Fin p) K}
    (hX : (X.map h.bar)ᵀ * G * X = G) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hNζ : h.norm ζ = 1) {P : GL (Fin p) K}
    (hP : X = (P : Matrix (Fin p) (Fin p) K) * diagonal (fun i : Fin p => ζ ^ (i : ℕ)) *
      ((P⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K)) :
    ∃ P' : GL (Fin p) K, X = (P' : Matrix (Fin p) (Fin p) K) *
      diagonal (fun i : Fin p => ζ ^ (i : ℕ)) * ((P'⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) ∧
      ((P' : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ * G * P' = 1 := by
  classical
  set Δ := diagonal (fun i : Fin p => ζ ^ (i : ℕ))
  set Pm := (P : Matrix (Fin p) (Fin p) K)
  set H := (Pm.map h.bar)ᵀ * G * Pm with hH
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne p)
  have hPP : ((P⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) * Pm = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hXP : X * Pm = Pm * Δ := by
    rw [hP, Matrix.mul_assoc, hPP, Matrix.mul_one]
  have hHΔ : H = (Δ.map h.bar)ᵀ * H * Δ := by
    calc H = (Pm.map h.bar)ᵀ * ((X.map h.bar)ᵀ * G * X) * Pm := by rw [hX]
      _ = ((X * Pm).map h.bar)ᵀ * G * (X * Pm) := (conjTranspose_mul_mul h G X Pm).symm
      _ = ((Pm * Δ).map h.bar)ᵀ * G * (Pm * Δ) := by rw [hXP]
      _ = (Δ.map h.bar)ᵀ * H * Δ := conjTranspose_mul_mul h G Pm Δ
  have hbar : h.bar ζ = ζ⁻¹ := bar_eq_inv_of_norm h hNζ
  have hoff : ∀ i j, i ≠ j → H i j = 0 := by
    intro i j hij
    have h1 := congrFun (congrFun hHΔ i) j
    rw [conjT_diagonal, mul_diagonal, diagonal_mul, map_pow, hbar] at h1
    have hne : (ζ⁻¹) ^ (i : ℕ) * ζ ^ (j : ℕ) ≠ 1 := by
      intro h2
      rw [inv_pow, inv_mul_eq_one₀ (pow_ne_zero _ hζ0)] at h2
      exact hij (Fin.ext (hζ.pow_inj i.2 j.2 h2))
    have h3 : H i j * (1 - (ζ⁻¹) ^ (i : ℕ) * ζ ^ (j : ℕ)) = 0 := by linear_combination h1
    exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 (Ne.symm hne))
  have hHu : IsUnit H.det := by
    have hdb : (Pm.map h.bar).det = h.bar Pm.det := (RingHom.map_det h.bar Pm).symm
    rw [hH, det_mul, det_mul, det_transpose, hdb]
    have hP' := (Matrix.isUnit_iff_isUnit_det _).1 P.isUnit
    exact ((hP'.map h.bar).mul ((Matrix.isUnit_iff_isUnit_det _).1 hGu)).mul hP'
  have hdiag : ∀ i, H i i ≠ 0 := by
    intro i h0
    have hrow : ∀ j, H i j = 0 := fun j => by
      by_cases hij : i = j
      · rw [← hij]; exact h0
      · exact hoff i j hij
    rw [det_eq_zero_of_row_eq_zero i hrow] at hHu
    exact not_isUnit_zero hHu
  have hHh : (H.map h.bar)ᵀ = H := by
    rw [hH, conjT_mul, conjT_mul, hGh, conjT_conjT, Matrix.mul_assoc]
  have hfix : ∀ i, h.bar (H i i)⁻¹ = (H i i)⁻¹ := fun i => by
    have h1 := congrFun (congrFun hHh i) i
    simp only [transpose_apply, map_apply] at h1
    rw [map_inv₀, h1]
  have hc : ∀ i, ∃ c : K, h.norm c = (H i i)⁻¹ := fun i => by
    obtain ⟨c, hc⟩ := h.normHom_surjective ⟨(H i i)⁻¹, h.mem_fixedField.2 (hfix i)⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  choose c hcn using hc
  have hc0 : ∀ i, c i ≠ 0 := fun i h0 => by
    have := hcn i
    rw [h0, UnitaryFieldData.norm, zero_mul] at this
    exact inv_ne_zero (hdiag i) this.symm
  set cu : Fin p → Kˣ := fun i => Units.mk0 (c i) (hc0 i)
  refine ⟨P * TauCeti.diagGL cu, ?_, ?_⟩
  · rw [_root_.mul_inv_rev, Units.val_mul, Units.val_mul, ← map_inv, TauCeti.diagGL_coe,
      TauCeti.diagGL_coe, hP]
    have hcomm : (diagonal fun i => ((cu i : Kˣ) : K)) * Δ =
        Δ * diagonal fun i => ((cu i : Kˣ) : K) := by
      rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      funext i
      ring
    have hinv : (diagonal fun i => ((cu i : Kˣ) : K)) *
        (diagonal fun i => ((cu⁻¹ i : Kˣ) : K)) = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      simp
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (diagonal _) Δ, hcomm, Matrix.mul_assoc Δ, ← Matrix.mul_assoc
      (diagonal fun i => ((cu i : Kˣ) : K)), hinv, Matrix.one_mul]
  · rw [Units.val_mul, conjTranspose_mul_mul, TauCeti.diagGL_coe, conjT_diagonal]
    ext i j
    rw [mul_diagonal, diagonal_mul]
    by_cases hij : i = j
    · subst hij
      rw [one_apply_eq]
      have := hcn i
      simp only [UnitaryFieldData.norm] at this
      simp only [cu, Units.val_mk0]
      calc h.bar (c i) * H i i * c i = (c i * h.bar (c i)) * H i i := by ring
        _ = 1 := by rw [this, inv_mul_cancel₀ (hdiag i)]
    · have h0 : ((((P : Matrix (Fin p) (Fin p) K)).map h.bar)ᵀ * G *
          (P : Matrix (Fin p) (Fin p) K)) i j = 0 := hoff i j hij
      rw [one_apply_ne hij, h0, mul_zero, zero_mul]

theorem reindex_conjTranspose_mul_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (G M : Matrix ι ι K) :
    ((reindex e e M).map h.bar)ᵀ * reindex e e G * reindex e e M =
      reindex e e ((M.map h.bar)ᵀ * G * M) := by
  have hmul : ∀ A B : Matrix ι ι K, reindex e e (A * B) = reindex e e A * reindex e e B :=
    fun A B => by
      rw [← coe_reindexAlgEquiv K K e, map_mul]
  have hmap : ∀ A : Matrix ι ι K, ((reindex e e A).map h.bar)ᵀ = reindex e e ((A.map h.bar)ᵀ) :=
    fun A => by
      ext i j
      rfl
  rw [hmul, hmul, hmap]

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
