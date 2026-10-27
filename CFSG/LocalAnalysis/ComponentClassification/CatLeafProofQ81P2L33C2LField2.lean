module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2LField

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {K : Type} [Field K]

theorem exists_gl_coboundary {σ : K ≃+* K} (hσσ : ∀ x, σ (σ x) = x) (hσ : σ ≠ 1)
    (B : Matrix (Fin n) (Fin n) K) (hB : B * B.map σ = 1) :
    ∃ H : GL (Fin n) K, B * (H : Matrix (Fin n) (Fin n) K).map σ = H := by
  classical
  set φ : (Fin n → K) → (Fin n → K) := fun v => B *ᵥ (σ ∘ v) with hφ
  have hφadd : ∀ v w, φ (v + w) = φ v + φ w := fun v w => by
    show B *ᵥ (σ ∘ (v + w)) = B *ᵥ (σ ∘ v) + B *ᵥ (σ ∘ w)
    rw [show (σ ∘ (v + w)) = σ ∘ v + σ ∘ w by ext i; simp, mulVec_add]
  have hφsmul : ∀ (c : K) v, φ (c • v) = σ c • φ v := fun c v => by
    show B *ᵥ (σ ∘ (c • v)) = σ c • (B *ᵥ (σ ∘ v))
    rw [show (σ ∘ (c • v)) = σ c • (σ ∘ v) by ext i; simp, mulVec_smul]
  have hφφ : ∀ v, φ (φ v) = v := fun v => by
    have e : σ ∘ (B *ᵥ (σ ∘ v)) = B.map σ *ᵥ v := by
      ext i
      simp only [Function.comp_apply, mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply,
        hσσ]
    rw [hφ]
    simp only
    rw [e, mulVec_mulVec, hB, one_mulVec]
  set T : Set (Fin n → K) := {v | φ v = v} with hT
  obtain ⟨l, hl⟩ : ∃ l : K, σ l ≠ l := by
    by_contra hc
    push Not at hc
    exact hσ (RingEquiv.ext hc)
  have hspan : Submodule.span K T = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hw₁ : v + φ v ∈ T := by
      change φ (v + φ v) = v + φ v
      rw [hφadd, hφφ, add_comm]
    have hw₂ : l • v + φ (l • v) ∈ T := by
      change φ (l • v + φ (l • v)) = l • v + φ (l • v)
      rw [hφadd, hφφ, add_comm]
    have hv : v = (l - σ l)⁻¹ • ((l • v + φ (l • v)) - σ l • (v + φ v)) := by
      rw [hφsmul, show l • v + σ l • φ v - σ l • (v + φ v) = (l - σ l) • v by
        rw [smul_add, sub_smul]; abel, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hl.symm),
        one_smul]
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span hw₂)
      (Submodule.smul_mem _ _ (Submodule.subset_span hw₁)))
  obtain ⟨b, hbT, hbspan, hbli⟩ := exists_linearIndependent K T
  let bb := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan, hspan])
  let b' := bb.reindex (bb.indexEquiv (Pi.basisFun K (Fin n)))
  have hb'T : ∀ j, φ (b' j) = b' j := fun j => by
    have : b' j ∈ T := by
      simp only [b', Module.Basis.reindex_apply, bb, Module.Basis.mk_apply]
      exact hbT (Subtype.mem _)
    exact this
  set H : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => b' j i with hH
  have hcol : H.col = ⇑b' := by
    ext j i
    rfl
  have hu : IsUnit H :=
    linearIndependent_cols_iff_isUnit.mp (by rw [hcol]; exact b'.linearIndependent)
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec]
  ext i j
  have := congrFun (hb'T j) i
  simp only [hφ, mulVec, dotProduct, Function.comp_apply] at this
  simp only [Matrix.mul_apply, Matrix.map_apply, hH, Matrix.of_apply]
  exact this

theorem hasWit_field [Finite K] (h2 : (2 : K) = 0) (hn : 3 ≤ n) {A : GL (Fin n) K}
    {σ : K ≃+* K} (hσ : σ ≠ 1) (hα : (conjAut n K A * fieldAut n K σ) ^ 2 = 1) :
    HasWit (conjAut n K A * fieldAut n K σ) := by
  have hsq : conjAut n K (A * GeneralLinearGroup.map (σ : K →+* K) A) *
      fieldAut n K (σ * σ) = 1 := by
    calc conjAut n K (A * GeneralLinearGroup.map (σ : K →+* K) A) * fieldAut n K (σ * σ) =
          conjAut n K A * (conjAut n K (GeneralLinearGroup.map (σ : K →+* K) A) *
            fieldAut n K σ) * fieldAut n K σ := by
          rw [map_mul, map_mul]; group
      _ = conjAut n K A * (fieldAut n K σ * conjAut n K A) * fieldAut n K σ := by
          rw [fieldAut_mul_conjAut]
      _ = 1 := by rw [← hα, sq]; group
  obtain ⟨hσσ', c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ hsq
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun τ : K ≃+* K => τ x) hσσ'
    exact this
  have hc' : GeneralLinearGroup.scalar (Fin n) c =
      A * CatalogueBHigherLinearField.glFieldAut (Fin n) K σ A := by
    rw [hc]
    rfl
  obtain ⟨b, hcoc, -⟩ := CatalogueBLinearSemilinear.exists_normalized_cocycle n (by omega) A σ
    (by rw [sq]; exact hσσ') hσ c hc'
  set B := GeneralLinearGroup.scalar (Fin n) b * A with hBdef
  have hB : (B : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K).map σ = 1 := by
    have := congrArg (fun X : GL (Fin n) K => (X : Matrix (Fin n) (Fin n) K)) hcoc
    simp only [Units.val_mul, Units.val_one] at this
    exact this
  obtain ⟨H, hH⟩ := exists_gl_coboundary hσσ hσ (B : Matrix (Fin n) (Fin n) K) hB
  have hBH : B * GeneralLinearGroup.map (σ : K →+* K) H = H := Units.ext hH
  have hBeq : B = H * (GeneralLinearGroup.map (σ : K →+* K) H)⁻¹ :=
    eq_mul_inv_of_mul_eq hBH
  have hAB : conjAut n K A = conjAut n K B := by
    rw [hBdef, map_mul, conjAut_scalar, one_mul]
  have hconj : conjAut n K A * fieldAut n K σ =
      conjAut n K H * fieldAut n K σ * (conjAut n K H)⁻¹ := by
    rw [← map_inv (conjAut n K) H, mul_assoc, fieldAut_mul_conjAut, ← mul_assoc, ← map_mul,
      map_inv, ← hBeq, hAB]
  rw [hconj]
  exact (hasWit_fieldAut h2 hn σ).conj (conjAut n K H)

end CFSG.ComponentClassification.HarrisLit.L33.C2
