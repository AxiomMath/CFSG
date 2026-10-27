module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

public section

namespace CFSG.UnitaryInvolutionIndex

open Matrix

variable {F : Type*} [Field F] {σ : F →+* F} {n : Type*} [Fintype n] [DecidableEq n]

@[expose] def unitaryGroup (h : (n → F) →ₛₗ[σ] (n → F) →ₗ[F] F) : Subgroup (GL n F) where
  carrier := {g | ∀ v w, h ((g : Matrix n n F) *ᵥ v) ((g : Matrix n n F) *ᵥ w) = h v w}
  one_mem' v w := by simp
  mul_mem' {g g'} hg hg' v w := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, ← mulVec_mulVec] at hg hg' ⊢
    rw [hg, hg']
  inv_mem' {g} hg v w := by
    have := hg ((g⁻¹ : GL n F) *ᵥ v) ((g⁻¹ : GL n F) *ᵥ w)
    simp only [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at this
    exact this.symm

theorem mem_unitaryGroup {h : (n → F) →ₛₗ[σ] (n → F) →ₗ[F] F} {g : GL n F} :
    g ∈ unitaryGroup h ↔
      ∀ v w, h ((g : Matrix n n F) *ᵥ v) ((g : Matrix n n F) *ᵥ w) = h v w :=
  Iff.rfl

@[expose] def specialUnitaryGroup (h : (n → F) →ₛₗ[σ] (n → F) →ₗ[F] F) :
    Subgroup (SpecialLinearGroup n F) :=
  (unitaryGroup h).comap SpecialLinearGroup.toGL

theorem mem_specialUnitaryGroup {h : (n → F) →ₛₗ[σ] (n → F) →ₗ[F] F}
    {g : SpecialLinearGroup n F} :
    g ∈ specialUnitaryGroup h ↔
      ∀ v w, h ((g : Matrix n n F) *ᵥ v) ((g : Matrix n n F) *ᵥ w) = h v w :=
  Iff.rfl

@[expose] def unitaryScalars (h : (n → F) →ₛₗ[σ] (n → F) →ₗ[F] F) :
    Subgroup (specialUnitaryGroup h) where
  carrier := {g | ∃ c : Fˣ,
    ((g : SpecialLinearGroup n F) : Matrix n n F) = scalar n (c : F)}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro g g' ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c * d, ?_⟩
    simp only [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, hc, hd, Units.val_mul, map_mul]
  inv_mem' := by
    rintro g ⟨c, hc⟩
    refine ⟨c⁻¹, ?_⟩
    have h1 : ((g : SpecialLinearGroup n F) : Matrix n n F) * scalar n ((c⁻¹ : Fˣ) : F) = 1 := by
      rw [hc, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    calc (((g⁻¹ : specialUnitaryGroup h) : SpecialLinearGroup n F) : Matrix n n F)
        = (((g⁻¹ : specialUnitaryGroup h) : SpecialLinearGroup n F) : Matrix n n F) *
            (((g : SpecialLinearGroup n F) : Matrix n n F) * scalar n ((c⁻¹ : Fˣ) : F)) := by
          rw [h1, Matrix.mul_one]
      _ = scalar n ((c⁻¹ : Fˣ) : F) := by
          rw [← Matrix.mul_assoc, ← SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul,
            inv_mul_cancel, Subgroup.coe_one, SpecialLinearGroup.coe_one, Matrix.one_mul]

theorem mem_unitaryScalars {h : (n → F) →ₛₗ[σ] (n → F) →ₗ[F] F} {g : specialUnitaryGroup h} :
    g ∈ unitaryScalars h ↔
      ∃ c : Fˣ, ((g : SpecialLinearGroup n F) : Matrix n n F) = scalar n (c : F) :=
  Iff.rfl

theorem mem_center_of_mem_unitaryScalars {h : (n → F) →ₛₗ[σ] (n → F) →ₗ[F] F}
    {g : specialUnitaryGroup h} (hg : g ∈ unitaryScalars h) : g ∈ Subgroup.center _ := by
  obtain ⟨c, hc⟩ := hg
  refine Subgroup.mem_center_iff.mpr fun x => Subtype.ext (Subtype.ext ?_)
  simp only [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, hc]
  exact ((scalar_commute (c : F) (fun r => Commute.all _ r) _).eq).symm

instance (h : (n → F) →ₛₗ[σ] (n → F) →ₗ[F] F) : (unitaryScalars h).Normal where
  conj_mem g hg x := by
    have hc := Subgroup.mem_center_iff.mp (mem_center_of_mem_unitaryScalars hg) x
    rw [hc, mul_inv_cancel_right]
    exact hg

abbrev projectiveSpecialUnitaryGroup (h : (n → F) →ₛₗ[σ] (n → F) →ₗ[F] F) : Type _ :=
  specialUnitaryGroup h ⧸ unitaryScalars h

omit [DecidableEq n] in
theorem mulVec_dotProduct_eq {R : Type*} [CommSemiring R] (A : Matrix n n R) (x z : n → R) :
    (A *ᵥ x) ⬝ᵥ z = x ⬝ᵥ (Aᵀ *ᵥ z) := by
  rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm, mulVec_transpose]

@[expose] def gram (h : (n → F) →ₛₗ[σ] (n → F) →ₗ[F] F) : Matrix n n F :=
  fun i j => h (Pi.single i 1) (Pi.single j 1)

theorem apply_eq_dotProduct_gram (h : (n → F) →ₛₗ[σ] (n → F) →ₗ[F] F) (v w : n → F) :
    h v w = (σ ∘ v) ⬝ᵥ (gram h *ᵥ w) := by
  have e := Matrix.toLinearMapₛₗ₂'_toMatrix' (R := F) (σ₁ := σ) (σ₂ := RingHom.id F) h
  conv_lhs => rw [← e]
  rw [Matrix.toLinearMapₛₗ₂'_apply]
  simp only [LinearMap.toMatrixₛₗ₂'_apply, RingHom.id_apply, smul_eq_mul, dotProduct, mulVec,
    Function.comp_apply, Finset.mul_sum, gram]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem transpose_map_mul_gram_mul {h : (n → F) →ₛₗ[σ] (n → F) →ₗ[F] F} {g : GL n F}
    (hg : g ∈ unitaryGroup h) :
    ((g : Matrix n n F).map σ)ᵀ * gram h * (g : Matrix n n F) = gram h := by
  ext i j
  have h1 := hg (Pi.single i 1) (Pi.single j 1)
  rw [apply_eq_dotProduct_gram, apply_eq_dotProduct_gram] at h1
  have hs : ∀ l : n, σ ∘ (Pi.single l 1 : n → F) = Pi.single l 1 := fun l => by
    ext a
    by_cases ha : a = l
    · subst ha
      simp
    · simp [ha]
  have hcol : σ ∘ ((g : Matrix n n F) *ᵥ Pi.single i 1) =
      ((g : Matrix n n F).map σ) *ᵥ Pi.single i 1 := by
    ext a
    rw [Function.comp_apply, RingHom.map_mulVec, hs]
  rw [hcol, hs, mulVec_dotProduct_eq, mulVec_mulVec, mulVec_mulVec] at h1
  simpa [gram, mulVec_single_one, dotProduct, Pi.single_apply] using h1

variable {k : Type*} [Field k] [Algebra F k]

@[expose] noncomputable def baseChange (h : (n → F) →ₛₗ[σ] (n → F) →ₗ[F] F) (φ : k →+* k) :
    (n → k) →ₛₗ[φ] (n → k) →ₗ[k] k :=
  Matrix.toLinearMapₛₗ₂' k φ (RingHom.id k) ((gram h).map (algebraMap F k))

theorem baseChange_apply (h : (n → F) →ₛₗ[σ] (n → F) →ₗ[F] F) (φ : k →+* k) (v w : n → k) :
    baseChange h φ v w = (φ ∘ v) ⬝ᵥ ((gram h).map (algebraMap F k) *ᵥ w) := by
  rw [baseChange, Matrix.toLinearMapₛₗ₂'_apply]
  simp only [RingHom.id_apply, smul_eq_mul, dotProduct, mulVec, Function.comp_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem baseChange_mulVec (h : (n → F) →ₛₗ[σ] (n → F) →ₗ[F] F) {φ : k →+* k}
    (hφ : ∀ c, φ (algebraMap F k c) = algebraMap F k (σ c)) {g : GL n F}
    (hg : g ∈ unitaryGroup h) (v w : n → k) :
    baseChange h φ (((g : Matrix n n F).map (algebraMap F k)) *ᵥ v)
      (((g : Matrix n n F).map (algebraMap F k)) *ᵥ w) = baseChange h φ v w := by
  rw [baseChange_apply, baseChange_apply]
  set G := (g : Matrix n n F).map (algebraMap F k)
  set H := (gram h).map (algebraMap F k)
  have hφG : φ ∘ (G *ᵥ v) = (G.map φ) *ᵥ (φ ∘ v) := by
    ext a
    rw [Function.comp_apply, RingHom.map_mulVec]
  have hGφ : G.map φ = ((g : Matrix n n F).map σ).map (algebraMap F k) := by
    ext a b
    simp [G, hφ]
  have hkey : (G.map φ)ᵀ * H * G = H := by
    rw [hGφ, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, transpose_map_mul_gram_mul hg]
  rw [hφG, mulVec_dotProduct_eq, mulVec_mulVec, mulVec_mulVec, hkey]

theorem det_gram_ne_zero {h : (n → F) →ₛₗ[σ] (n → F) →ₗ[F] F} (hh : h.Nondegenerate) :
    (gram h).det ≠ 0 := by
  intro h0
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  exact hw0 (hh.2 w fun v => by rw [apply_eq_dotProduct_gram, hw, dotProduct_zero])

theorem baseChange_separatingLeft {h : (n → F) →ₛₗ[σ] (n → F) →ₗ[F] F} (hh : h.Nondegenerate)
    {φ : k →+* k} (hφ : Function.Injective φ) : (baseChange h φ).SeparatingLeft := by
  intro v hv
  have hdet : ((gram h).map (algebraMap F k)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).mpr (det_gram_ne_zero hh)
  have hvec : (φ ∘ v) ᵥ* (gram h).map (algebraMap F k) = 0 := by
    ext j
    have := hv (Pi.single j 1)
    rw [baseChange_apply, dotProduct_mulVec] at this
    simpa [dotProduct, Pi.single_apply] using this
  by_contra hv0
  have hφv : φ ∘ v ≠ 0 := by
    intro h0
    apply hv0
    ext i
    have := congrFun h0 i
    rw [Function.comp_apply, Pi.zero_apply] at this
    exact hφ (this.trans (map_zero φ).symm)
  exact hdet (Matrix.exists_vecMul_eq_zero_iff.mp ⟨φ ∘ v, hφv, hvec⟩)

end CFSG.UnitaryInvolutionIndex
