module

public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.ABGLocalTools

open Matrix

section Norm

variable {F : Type*} [Field F] [Finite F]

theorem exists_prod_pow_eq (σ : F ≃+* F) {c : F} (hc : σ c = c) :
    ∃ d : F, ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) d = c := by
  classical
  have : Finite (F ≃+* F) :=
    Finite.of_injective (fun τ : F ≃+* F => (τ : F → F)) (fun _ _ h => RingEquiv.ext (congrFun h))
  let H : Subgroup (F ≃+* F) := Subgroup.zpowers σ
  have : Fintype H := Fintype.ofFinite H
  let F₀ := FixedPoints.subfield H F
  have hstab : H ≤ MulAction.stabilizer (F ≃+* F) c := by
    rw [Subgroup.zpowers_le]
    exact hc
  have hcF₀ : c ∈ F₀ := by
    intro h
    exact hstab h.property
  obtain ⟨d, hd⟩ := FiniteField.norm_surjective F₀ F ⟨c, hcF₀⟩
  refine ⟨d, ?_⟩
  have hnorm := Algebra.norm_eq_prod_automorphisms F₀ d
  rw [hd] at hnorm
  have hσfin : IsOfFinOrder σ := isOfFinOrder_of_finite σ
  calc ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) d
      = ∏ i : Fin (orderOf σ), (σ ^ (i : ℕ)) d := (Fin.prod_univ_eq_prod_range _ _).symm
    _ = ∏ h : H, (h : F ≃+* F) d :=
        Fintype.prod_equiv (finEquivZPowers hσfin) _ _ (fun i => by
          rw [finEquivZPowers_apply])
    _ = ∏ τ : Gal(F/F₀), τ d :=
        Fintype.prod_equiv (FixedPoints.toAlgAutMulEquiv H F).toEquiv _ _ (fun h => rfl)
    _ = c := hnorm.symm

end Norm

section Speiser

variable {F : Type*} [Field F]

theorem iterate_smul_of_semilinear (σ : F ≃+* F) {ψ : (Fin 2 → F) → (Fin 2 → F)}
    (hsmul : ∀ (a : F) (v : Fin 2 → F), ψ (a • v) = σ a • ψ v) (k : ℕ) (a : F)
    (v : Fin 2 → F) : ψ^[k] (a • v) = (σ ^ k) a • ψ^[k] v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hsmul, pow_succ',
      RingAut.mul_apply]

theorem exists_fixed_of_iterate_eq_id (σ : F ≃+* F) (hpos : 0 < orderOf σ)
    {ψ : (Fin 2 → F) → (Fin 2 → F)} (hadd : ∀ v w, ψ (v + w) = ψ v + ψ w)
    (hsmul : ∀ (a : F) (v : Fin 2 → F), ψ (a • v) = σ a • ψ v)
    (hpow : ∀ v, ψ^[orderOf σ] v = v) : ∃ v : Fin 2 → F, v ≠ 0 ∧ ψ v = v := by
  classical
  set n := orderOf σ with hn
  let ψA : (Fin 2 → F) →+ (Fin 2 → F) := AddMonoidHom.mk' ψ hadd
  let e₀ : Fin 2 → F := Pi.single 0 1
  let S : F → (Fin 2 → F) := fun a => ∑ i ∈ Finset.range n, ψ^[i] (a • e₀)
  have hfix : ∀ a, ψ (S a) = S a := by
    intro a
    have h1 : ψ (S a) = ∑ i ∈ Finset.range n, ψ^[i + 1] (a • e₀) := by
      change ψA (∑ i ∈ Finset.range n, ψ^[i] (a • e₀)) = _
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Function.iterate_succ_apply']
      rfl
    have h2 := Finset.sum_range_succ' (fun i => ψ^[i] (a • e₀)) n
    have h3 := Finset.sum_range_succ (fun i => ψ^[i] (a • e₀)) n
    rw [h1]
    simp only [Function.iterate_zero, id_eq] at h2
    rw [hpow] at h3
    have h4 := h2.symm.trans h3
    exact add_right_cancel h4
  obtain ⟨a, ha⟩ : ∃ a, S a ≠ 0 := by
    by_contra hall
    simp only [ne_eq, not_exists, not_not] at hall
    let coef : Fin n → F := fun i => (ψ^[(i : ℕ)] e₀) 0
    let chars : Fin n → (F →* F) := fun i => ((σ ^ (i : ℕ) : F ≃+* F) : F →* F)
    have hinj : Function.Injective chars := by
      intro i j hij
      have h : (σ ^ (i : ℕ) : F ≃+* F) = σ ^ (j : ℕ) := by
        ext x
        exact DFunLike.congr_fun hij x
      exact Fin.ext (pow_injOn_Iio_orderOf (Set.mem_Iio.mpr i.isLt) (Set.mem_Iio.mpr j.isLt) h)
    have hli := (linearIndependent_monoidHom F F).comp chars hinj
    have hsum : ∑ i, coef i • ((fun f : F →* F => (f : F → F)) ∘ chars) i = 0 := by
      funext x
      have hx := congrFun (hall x) 0
      simp only [S, Finset.sum_apply, Pi.zero_apply] at hx
      simp only [Finset.sum_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply]
      rw [← hx, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [iterate_smul_of_semilinear σ hsmul, Pi.smul_apply, smul_eq_mul, mul_comm]
      rfl
    have h0 := Fintype.linearIndependent_iff.mp hli coef hsum ⟨0, hpos⟩
    simp [coef, e₀] at h0
  exact ⟨S a, ha, hfix a⟩

end Speiser

section Eigenvector

variable {F : Type*} [Field F]

@[expose] noncomputable def glNorm (σ : F ≃+* F) (G : GL (Fin 2) F) : ℕ → GL (Fin 2) F
  | 0 => 1
  | k + 1 => glNorm σ G k * GeneralLinearGroup.map ((σ ^ k : F ≃+* F) : F →+* F) G

theorem glNorm_zero (σ : F ≃+* F) (G : GL (Fin 2) F) : glNorm σ G 0 = 1 := rfl

theorem glNorm_succ (σ : F ≃+* F) (G : GL (Fin 2) F) (k : ℕ) :
    glNorm σ G (k + 1) = glNorm σ G k * GeneralLinearGroup.map ((σ ^ k : F ≃+* F) : F →+* F) G :=
  rfl

theorem iterate_semilinear_apply (σ : F ≃+* F) (G : GL (Fin 2) F) (k : ℕ) (v : Fin 2 → F) :
    (fun w : Fin 2 → F => (G : Matrix (Fin 2) (Fin 2) F) *ᵥ (fun i => σ (w i)))^[k] v =
      (glNorm σ G k : Matrix (Fin 2) (Fin 2) F) *ᵥ (fun i => (σ ^ k) (v i)) := by
  induction k generalizing v with
  | zero => simp [glNorm_zero]
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, glNorm_succ, Units.val_mul, ← Matrix.mulVec_mulVec]
    congr 1
    funext i
    have h := RingHom.map_mulVec ((σ ^ k : F ≃+* F) : F →+* F)
      (G : Matrix (Fin 2) (Fin 2) F) (fun j => σ (v j)) i
    simp only [RingEquiv.coe_toRingHom, Function.comp_def] at h
    rw [h]
    congr 1

theorem exists_eigenvector_of_glNorm_scalar [Finite F] (σ : F ≃+* F) (G : GL (Fin 2) F) {c : F}
    (hc : ((glNorm σ G (orderOf σ) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.scalar (Fin 2) c) :
    ∃ v : Fin 2 → F, v ≠ 0 ∧ ∃ μ : F,
      (G : Matrix (Fin 2) (Fin 2) F) *ᵥ (fun i => σ (v i)) = μ • v := by
  classical
  have : Finite (F ≃+* F) :=
    Finite.of_injective (fun τ : F ≃+* F => (τ : F → F)) (fun _ _ h => RingEquiv.ext (congrFun h))
  set n := orderOf σ with hn
  have hpos : 0 < n := (isOfFinOrder_of_finite σ).orderOf_pos
  set φ : (Fin 2 → F) → (Fin 2 → F) :=
    fun w => (G : Matrix (Fin 2) (Fin 2) F) *ᵥ (fun i => σ (w i)) with hφ
  have hφadd : ∀ v w, φ (v + w) = φ v + φ w := by
    intro v w
    simp only [φ, Pi.add_apply, map_add]
    rw [← Matrix.mulVec_add]
    rfl
  have hφsmul : ∀ (a : F) (v : Fin 2 → F), φ (a • v) = σ a • φ v := by
    intro a v
    simp only [φ, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [← Matrix.mulVec_smul]
    rfl
  have hφn : ∀ v, φ^[n] v = c • v := by
    intro v
    rw [hφ, iterate_semilinear_apply, hc, pow_orderOf_eq_one]
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply]
  set e₀ : Fin 2 → F := Pi.single 0 1 with he₀def
  have he₀ : φ e₀ ≠ 0 := by
    intro h
    have hσe : (fun i => σ (e₀ i)) = e₀ := by
      funext i
      fin_cases i <;> simp [e₀]
    simp only [φ, hσe] at h
    have h2 := congrArg (fun w => ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w) h
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h2
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h2
    have h3 := congrFun h2 0
    simp [e₀] at h3
  have hσc : σ c = c := by
    have h1 : φ (φ^[n] e₀) = φ^[n] (φ e₀) :=
      (Function.iterate_succ_apply' φ n e₀).symm.trans (Function.iterate_succ_apply φ n e₀)
    rw [hφn, hφn, hφsmul] at h1
    exact smul_left_injective F he₀ h1
  have hc0 : c ≠ 0 := by
    intro h0
    have hdet := congrArg Matrix.det hc
    rw [h0, map_zero, Matrix.det_zero] at hdet
    exact (glNorm σ G n).det_ne_zero hdet
  obtain ⟨d, hd⟩ := exists_prod_pow_eq σ hσc
  rw [← hn] at hd
  have hd0 : d ≠ 0 := by
    intro h0
    apply hc0
    rw [← hd, h0, Finset.prod_eq_zero (i := 0) (Finset.mem_range.mpr hpos) (by simp)]
  set ψ : (Fin 2 → F) → (Fin 2 → F) := fun w => d⁻¹ • φ w with hψ
  have hψadd : ∀ v w, ψ (v + w) = ψ v + ψ w := by
    intro v w
    simp only [ψ, hφadd, smul_add]
  have hψsmul : ∀ (a : F) (v : Fin 2 → F), ψ (a • v) = σ a • ψ v := by
    intro a v
    simp only [ψ, hφsmul, smul_smul, mul_comm]
  have hψiter : ∀ k v, ψ^[k] v = (∏ i ∈ Finset.range k, (σ ^ i) d)⁻¹ • φ^[k] v := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply]
      simp only [ψ]
      rw [iterate_smul_of_semilinear σ hφsmul, smul_smul, Finset.prod_range_succ, map_inv₀,
        mul_inv]
  have hψn : ∀ v, ψ^[n] v = v := by
    intro v
    rw [hψiter, hd, hφn, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  obtain ⟨v, hv0, hv⟩ := exists_fixed_of_iterate_eq_id σ hpos hψadd hψsmul hψn
  refine ⟨v, hv0, d, ?_⟩
  have h1 : d • ψ v = d • v := by rw [hv]
  simp only [ψ, smul_smul, mul_inv_cancel₀ hd0, one_smul] at h1
  exact h1

end Eigenvector

end CFSG.ABGLocalTools
