module

public import CFSG.LieType.Chevalley.E6A5CubeFixed
public import CFSG.LieType.Universal.Unitary.Basic

public noncomputable section

namespace CFSG.LieType.Chevalley.E6A5Cube

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.ExteriorCube exteriorPower
  Set Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)

variable {K : Type} [Field K]

variable (K) in
@[expose] def eDiag (ζ : K) : Fin 6 → K := ![ζ, -ζ, ζ, 1, 1, 1]

theorem eDiag_ne_zero {ζ : K} (hζ : ζ ≠ 0) (i : Fin 6) : eDiag K ζ i ≠ 0 := by
  fin_cases i <;> simp [eDiag, hζ]

theorem diagonal_mul_antiDiag_mul_diagonal (d s e : Fin 6 → K) :
    diagonal d * antiDiag K s * diagonal e = antiDiag K fun i => d i * s i * e (Fin.rev i) := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, antiDiag_apply]
  by_cases h : j = Fin.rev i
  · subst h
    simp
  · simp [h]

theorem antidiag_eq_antiDiag : (antidiag 6 : Matrix (Fin 6) (Fin 6) K) = antiDiag K fun _ => 1 := by
  ext i j
  simp [CFSG.LieType.Universal.Unitary.antidiag, antiDiag_apply]

theorem key_identity (σ : K →+* K) {ζ : K} (hσζ : σ ζ = -ζ) :
    diagonal (fun i => σ (eDiag K ζ i)) * signAntiInv K * diagonal (eDiag K ζ) =
      ζ • (antidiag 6 : Matrix (Fin 6) (Fin 6) K) := by
  rw [signAntiInv, diagonal_mul_antiDiag_mul_diagonal, antidiag_eq_antiDiag]
  ext i j
  simp only [Matrix.smul_apply, antiDiag_apply, smul_eq_mul]
  by_cases h : j = Fin.rev i
  · subst h
    simp only [if_true, mul_one]
    fin_cases i <;> simp [eDiag, hσζ] <;> ring
  · simp [h]

theorem coe_map_sl (σ : K →+* K) (h : SpecialLinearGroup (Fin 6) K) :
    ((SpecialLinearGroup.map σ h : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      (h : Matrix (Fin 6) (Fin 6) K).map σ := by
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]

theorem tauSL_eq_iff (σ : K →+* K) (h : SpecialLinearGroup (Fin 6) K) :
    tauSL K σ h = h ↔
      ((h : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ * signAntiInv K * (h : Matrix (Fin 6) (Fin 6) K) =
        signAntiInv K := by
  set W : SpecialLinearGroup (Fin 6) K := SpecialLinearGroup.map σ h with hW
  have hWm : (W : Matrix (Fin 6) (Fin 6) K) = (h : Matrix (Fin 6) (Fin 6) K).map σ :=
    coe_map_sl σ h
  set a : Matrix (Fin 6) (Fin 6) K := ((W⁻¹ : SpecialLinearGroup (Fin 6) K) :
    Matrix (Fin 6) (Fin 6) K)ᵀ with ha
  have h1 : (W : Matrix (Fin 6) (Fin 6) K)ᵀ * a = 1 := by
    rw [ha, ← transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
    simp
  have h2 : a * (W : Matrix (Fin 6) (Fin 6) K)ᵀ = 1 := by
    rw [ha, ← transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
    simp
  have hM1 : signAnti K * signAntiInv K = 1 := signAnti_mul_inv
  have hM2 : signAntiInv K * signAnti K = 1 := signAntiInv_mul
  have hτ : (tauSL K σ h : Matrix (Fin 6) (Fin 6) K) = signAnti K * a * signAntiInv K := rfl
  rw [← hWm]
  constructor
  · intro hh
    have hh' := congrArg (fun x : SpecialLinearGroup (Fin 6) K => (x : Matrix (Fin 6) (Fin 6) K)) hh
    simp only [hτ] at hh'
    calc (W : Matrix (Fin 6) (Fin 6) K)ᵀ * signAntiInv K * (h : Matrix (Fin 6) (Fin 6) K)
        = (W : Matrix (Fin 6) (Fin 6) K)ᵀ * signAntiInv K * (signAnti K * a * signAntiInv K) := by
          rw [hh']
      _ = ((W : Matrix (Fin 6) (Fin 6) K)ᵀ * (signAntiInv K * signAnti K)) * a * signAntiInv K := by
          simp only [Matrix.mul_assoc]
      _ = signAntiInv K := by rw [hM2, Matrix.mul_one, h1, Matrix.one_mul]
  · intro hh
    apply Subtype.ext
    rw [hτ]
    calc signAnti K * a * signAntiInv K
        = signAnti K * (a * ((W : Matrix (Fin 6) (Fin 6) K)ᵀ * signAntiInv K *
            (h : Matrix (Fin 6) (Fin 6) K))) := by
          rw [hh]
          simp only [Matrix.mul_assoc]
      _ = signAnti K * ((a * (W : Matrix (Fin 6) (Fin 6) K)ᵀ) * signAntiInv K *
            (h : Matrix (Fin 6) (Fin 6) K)) := by simp only [Matrix.mul_assoc]
      _ = (h : Matrix (Fin 6) (Fin 6) K) := by
          rw [h2, Matrix.one_mul, ← Matrix.mul_assoc, hM1, Matrix.one_mul]

theorem diag_mul_inv (e : Fin 6 → K) (he : ∀ i, e i ≠ 0) :
    diagonal e * diagonal (fun i => (e i)⁻¹) = 1 := by
  rw [diagonal_mul_diagonal]
  have : (fun i => e i * (e i)⁻¹) = fun _ => (1 : K) := funext fun i => mul_inv_cancel₀ (he i)
  rw [this]
  exact diagonal_one

theorem diag_inv_mul (e : Fin 6 → K) (he : ∀ i, e i ≠ 0) :
    diagonal (fun i => (e i)⁻¹) * diagonal e = 1 := by
  rw [diagonal_mul_diagonal]
  have : (fun i => (e i)⁻¹ * e i) = fun _ => (1 : K) := funext fun i => inv_mul_cancel₀ (he i)
  rw [this]
  exact diagonal_one

variable (K) in
@[expose] def conjDiag (e : Fin 6 → K) (he : ∀ i, e i ≠ 0) :
    SpecialLinearGroup (Fin 6) K →* SpecialLinearGroup (Fin 6) K where
  toFun h := ⟨diagonal e * (h : Matrix (Fin 6) (Fin 6) K) * diagonal (fun i => (e i)⁻¹), by
    rw [det_mul, det_mul, det_diagonal, det_diagonal, h.2, mul_one, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => mul_inv_cancel₀ (he i)⟩
  map_one' := Subtype.ext (by
    change diagonal e * (1 : Matrix (Fin 6) (Fin 6) K) * diagonal (fun i => (e i)⁻¹) = 1
    rw [Matrix.mul_one, diag_mul_inv e he])
  map_mul' g h := Subtype.ext (by
    change diagonal e * ((g : Matrix (Fin 6) (Fin 6) K) * (h : Matrix (Fin 6) (Fin 6) K)) *
        diagonal (fun i => (e i)⁻¹) =
      diagonal e * (g : Matrix (Fin 6) (Fin 6) K) * diagonal (fun i => (e i)⁻¹) *
        (diagonal e * (h : Matrix (Fin 6) (Fin 6) K) * diagonal (fun i => (e i)⁻¹))
    have h1 := diag_inv_mul e he
    calc diagonal e * ((g : Matrix (Fin 6) (Fin 6) K) * (h : Matrix (Fin 6) (Fin 6) K)) *
          diagonal (fun i => (e i)⁻¹)
        = diagonal e * (g : Matrix (Fin 6) (Fin 6) K) * (diagonal (fun i => (e i)⁻¹) *
            diagonal e) * (h : Matrix (Fin 6) (Fin 6) K) * diagonal (fun i => (e i)⁻¹) := by
          rw [h1, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc])

theorem coe_conjDiag (e : Fin 6 → K) (he : ∀ i, e i ≠ 0) (h : SpecialLinearGroup (Fin 6) K) :
    (conjDiag K e he h : Matrix (Fin 6) (Fin 6) K) =
      diagonal e * (h : Matrix (Fin 6) (Fin 6) K) * diagonal (fun i => (e i)⁻¹) := rfl

theorem sandwich_cancel {U Ui V Vi A B : Matrix (Fin 6) (Fin 6) K} (h1 : U * Ui = 1)
    (h2 : Vi * V = 1) (H : Ui * A * Vi = Ui * B * Vi) : A = B := by
  calc A = (U * Ui) * A * (Vi * V) := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    _ = U * (Ui * A * Vi) * V := by simp only [Matrix.mul_assoc]
    _ = U * (Ui * B * Vi) * V := by rw [H]
    _ = (U * Ui) * B * (Vi * V) := by simp only [Matrix.mul_assoc]
    _ = B := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem mem_SUM_conjDiag_iff (σ : K ≃+* K) {ζ : K} (hζ : ζ ≠ 0) (hσζ : σ ζ = -ζ)
    (h : SpecialLinearGroup (Fin 6) K) :
    conjDiag K (eDiag K ζ) (eDiag_ne_zero hζ) h ∈ SUM K σ.toRingHom ↔
      conjTr σ (h : Matrix (Fin 6) (Fin 6) K) * antidiag 6 * (h : Matrix (Fin 6) (Fin 6) K) =
        antidiag 6 := by
  have he := eDiag_ne_zero hζ
  have hkey := key_identity σ.toRingHom hσζ
  rw [mem_SUM_iff, tauSL_eq_iff, coe_conjDiag]
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at hkey ⊢
  generalize eDiag K ζ = e at *
  have hσe : ∀ i, σ (e i) ≠ 0 := fun i => by simpa using he i
  set hm : Matrix (Fin 6) (Fin 6) K := (h : Matrix (Fin 6) (Fin 6) K) with hhm
  set J : Matrix (Fin 6) (Fin 6) K := antidiag 6 with hJ
  have hσE1 : diagonal (fun i => σ (e i)) * diagonal (fun i => (σ (e i))⁻¹) = 1 :=
    diag_mul_inv _ hσe
  have hσE2 : diagonal (fun i => (σ (e i))⁻¹) * diagonal (fun i => σ (e i)) = 1 :=
    diag_inv_mul _ hσe
  have hE1 : diagonal (fun i => (e i)⁻¹) * diagonal e = 1 := diag_inv_mul e he
  have hE2 : diagonal e * diagonal (fun i => (e i)⁻¹) = 1 := diag_mul_inv e he
  have hmap : (diagonal e * hm * diagonal (fun i => (e i)⁻¹)).map σ =
      diagonal (fun i => σ (e i)) * hm.map σ * diagonal (fun i => (σ (e i))⁻¹) := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero σ),
      Matrix.diagonal_map (map_zero σ)]
    simp [Function.comp_def]
  have hL : ((diagonal e * hm * diagonal (fun i => (e i)⁻¹)).map σ)ᵀ *
        signAntiInv K * (diagonal e * hm * diagonal (fun i => (e i)⁻¹)) =
      diagonal (fun i => (σ (e i))⁻¹) * (ζ • ((hm.map σ)ᵀ * J * hm)) *
        diagonal (fun i => (e i)⁻¹) := by
    rw [hmap, transpose_mul, transpose_mul, diagonal_transpose, diagonal_transpose]
    calc _ = diagonal (fun i => (σ (e i))⁻¹) * (hm.map σ)ᵀ *
            (diagonal (fun i => σ (e i)) * signAntiInv K * diagonal e) * hm *
              diagonal (fun i => (e i)⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hkey]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have hR : signAntiInv K = diagonal (fun i => (σ (e i))⁻¹) * (ζ • J) *
      diagonal (fun i => (e i)⁻¹) := by
    rw [← hkey]
    calc signAntiInv K
        = (diagonal (fun i => (σ (e i))⁻¹) * diagonal (fun i => σ (e i))) * signAntiInv K *
            (diagonal e * diagonal (fun i => (e i)⁻¹)) := by
          rw [hσE2, hE2, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [hL, hR]
  constructor
  · intro H
    have H' := sandwich_cancel hσE1 hE1 H
    have H'' : (ζ • ((hm.map σ)ᵀ * J * hm)) = ζ • J := H'
    exact smul_right_injective _ hζ H''
  · intro H
    have : (hm.map σ)ᵀ * J * hm = J := H
    rw [this]

@[expose] def suToSL (σ : K ≃+* K) : SU σ 6 →* SpecialLinearGroup (Fin 6) K where
  toFun x := ⟨((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K), x.2.1⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul, Units.val_mul]; rfl)

variable (σ : K ≃+* K) {ζ : K} (hζ : ζ ≠ 0)

@[expose] def conjSU : SU σ 6 →* SpecialLinearGroup (Fin 6) K :=
  (conjDiag K (eDiag K ζ) (eDiag_ne_zero hζ)).comp (suToSL σ)

include hζ in
theorem conjSU_mem_SUM (hσζ : σ ζ = -ζ) (x : SU σ 6) : conjSU σ hζ x ∈ SUM K σ.toRingHom :=
  (mem_SUM_conjDiag_iff σ hζ hσζ _).2 x.2.2

theorem conjDiag_conjDiag_inv (e : Fin 6 → K) (he : ∀ i, e i ≠ 0) (he' : ∀ i, (e i)⁻¹ ≠ 0)
    (h : SpecialLinearGroup (Fin 6) K) :
    conjDiag K e he (conjDiag K (fun i => (e i)⁻¹) he' h) = h := by
  apply Subtype.ext
  simp only [coe_conjDiag, inv_inv]
  have h1 := diag_mul_inv e he
  have h2 := diag_inv_mul e he
  calc diagonal e * (diagonal (fun i => (e i)⁻¹) * (h : Matrix (Fin 6) (Fin 6) K) * diagonal e) *
        diagonal (fun i => (e i)⁻¹)
      = (diagonal e * diagonal (fun i => (e i)⁻¹)) * (h : Matrix (Fin 6) (Fin 6) K) *
          (diagonal e * diagonal (fun i => (e i)⁻¹)) := by simp only [Matrix.mul_assoc]
    _ = h := by rw [h1, Matrix.one_mul, Matrix.mul_one]

include hζ in
theorem exists_conjSU_eq (hσζ : σ ζ = -ζ) {h' : SpecialLinearGroup (Fin 6) K}
    (hh' : h' ∈ SUM K σ.toRingHom) : ∃ x : SU σ 6, conjSU σ hζ x = h' := by
  have he := eDiag_ne_zero hζ
  have he' : ∀ i, (eDiag K ζ i)⁻¹ ≠ 0 := fun i => inv_ne_zero (he i)
  set h : SpecialLinearGroup (Fin 6) K := conjDiag K (fun i => (eDiag K ζ i)⁻¹) he' h' with hh
  have hcj : conjDiag K (eDiag K ζ) he h = h' := conjDiag_conjDiag_inv _ he he' h'
  have hcond := (mem_SUM_conjDiag_iff σ hζ hσζ h).1 (by rw [hcj]; exact hh')
  refine ⟨⟨Matrix.SpecialLinearGroup.toGL h, ⟨?_, ?_⟩⟩, ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact h.2
  · rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact hcond
  · apply Subtype.ext
    change (conjDiag K (eDiag K ζ) he (suToSL σ ⟨Matrix.SpecialLinearGroup.toGL h, _⟩) :
      Matrix (Fin 6) (Fin 6) K) = _
    rw [← hcj]
    rfl

section Levi

variable [Finite K]

variable (K) in
@[expose] def fixA (σ : K →+* K) : Subgroup (groupA K) :=
  MonoidHom.eqLocus (twistA K σ) (MonoidHom.id _)

theorem mem_fixA_iff {σ : K →+* K} {g : groupA K} : g ∈ fixA K σ ↔ twistA K σ g = g := Iff.rfl

@[expose] def leviHomA : SU σ 6 →* groupA K := (liftA K).comp (conjSU σ hζ)

include hζ in
theorem leviHomA_mem_fixA (hσζ : σ ζ = -ζ) (x : SU σ 6) : leviHomA σ hζ x ∈ fixA K σ.toRingHom :=
  twistA_liftA_of_mem_SUM σ.toRingHom (conjSU_mem_SUM σ hζ hσζ x)

@[expose] def leviHom (hσζ : σ ζ = -ζ) : SU σ 6 →* fixA K σ.toRingHom :=
  (leviHomA σ hζ).codRestrict _ (leviHomA_mem_fixA σ hζ hσζ)

theorem coe_leviHom (hσζ : σ ζ = -ζ) (x : SU σ 6) :
    ((leviHom σ hζ hσζ x : fixA K σ.toRingHom) : groupA K) = leviHomA σ hζ x := rfl

theorem leviHom_surjective (hσσ : ∀ c, σ (σ c) = c) (hσζ : σ ζ = -ζ) :
    Function.Surjective (leviHom σ hζ hσζ) := by
  rintro ⟨g, hg⟩
  obtain ⟨h', hh', hψ⟩ := exists_mem_SUM_of_twist_fixed (σ := σ.toRingHom)
    (fun c => by simpa using hσσ c) hg
  obtain ⟨x, hx⟩ := exists_conjSU_eq σ hζ hσζ hh'
  refine ⟨x, Subtype.ext ?_⟩
  rw [coe_leviHom, leviHomA, MonoidHom.comp_apply, hx]
  exact liftA_eq_of_psiA_eq hψ

theorem leviHom_eq_one (hσζ : σ ζ = -ζ) {x : SU σ 6} (hx : leviHom σ hζ hσζ x = 1) :
    ∃ l : K, ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = l • (1 : Matrix (Fin 6) (Fin 6) K) := by
  have h1 : leviHomA σ hζ x = 1 := congrArg Subtype.val hx
  rw [leviHomA, MonoidHom.comp_apply] at h1
  have h2 : cubeHom (conjSU σ hζ x) = 1 := by
    rw [← psiA_liftA, h1, map_one]
  obtain ⟨l, -, hl⟩ := (cubeHom_eq_one_iff _).1 h2
  refine ⟨l, ?_⟩
  have he := eDiag_ne_zero hζ
  have hx' : (conjSU σ hζ x : Matrix (Fin 6) (Fin 6) K) =
      diagonal (eDiag K ζ) * ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        diagonal (fun i => (eDiag K ζ i)⁻¹) := rfl
  rw [hx'] at hl
  have h3 := diag_inv_mul (eDiag K ζ) he
  have h4 := diag_mul_inv (eDiag K ζ) he
  calc ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
      = (diagonal (fun i => (eDiag K ζ i)⁻¹) * diagonal (eDiag K ζ)) *
          ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
            (diagonal (fun i => (eDiag K ζ i)⁻¹) * diagonal (eDiag K ζ)) := by
        rw [h3, Matrix.one_mul, Matrix.mul_one]
    _ = diagonal (fun i => (eDiag K ζ i)⁻¹) * (diagonal (eDiag K ζ) *
          ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
            diagonal (fun i => (eDiag K ζ i)⁻¹)) * diagonal (eDiag K ζ) := by
        simp only [Matrix.mul_assoc]
    _ = l • (1 : Matrix (Fin 6) (Fin 6) K) := by
        rw [hl, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h3]

theorem leviHom_scalar_sq (hσζ : σ ζ = -ζ) {z : SU σ 6} {l : K}
    (hz : ((z : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = l • (1 : Matrix (Fin 6) (Fin 6) K)) :
    leviHom σ hζ hσζ (z * z) = 1 := by
  have hdet : l ^ 6 = 1 := by
    have := z.2.1
    rw [hz, Matrix.det_smul, det_one, mul_one, Fintype.card_fin] at this
    exact this
  have hl3 : (l ^ 2) ^ 3 = 1 := by rw [← pow_mul]; exact hdet
  have hl6 : (l ^ 2) ^ 6 = 1 := by rw [show 6 = 3 * 2 from rfl, pow_mul, hl3, one_pow]
  have he := eDiag_ne_zero hζ
  have hz2 : (((z * z : SU σ 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      (l ^ 2) • (1 : Matrix (Fin 6) (Fin 6) K) := by
    rw [Subgroup.coe_mul, Units.val_mul, hz, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
      smul_smul, pow_two]
  have h1 : conjSU σ hζ (z * z) = scalarSL K (l ^ 2) hl6 := by
    apply Subtype.ext
    change diagonal (eDiag K ζ) * (((z * z : SU σ 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      diagonal (fun i => (eDiag K ζ i)⁻¹) = (l ^ 2) • (1 : Matrix (Fin 6) (Fin 6) K)
    rw [hz2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, diag_mul_inv _ he]
  apply Subtype.ext
  rw [coe_leviHom, leviHomA, MonoidHom.comp_apply, h1]
  exact liftA_eq_of_psiA_eq (g := 1) (by rw [map_one, cubeHom_scalarSL hl3])

end Levi

end CFSG.LieType.Chevalley.E6A5Cube
