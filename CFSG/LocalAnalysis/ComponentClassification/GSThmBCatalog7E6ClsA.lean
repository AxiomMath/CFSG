module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7E6Tor

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CatFactsSp4

namespace Cat7E6

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag

variable {K : Type} [Field K]

theorem false_of_sq_det (h2 : (2 : K) ≠ 0) {d : K} (hd0 : d ≠ 0) (hdsq : ∀ l : K, l ^ 2 ≠ d)
    {g : Matrix (Fin 2) (Fin 2) K} (hgg : g * g = d • 1) (hdet : g.det = d) : False := by
  have e00 := congrFun (congrFun hgg 0) 0
  have e01 := congrFun (congrFun hgg 0) 1
  have e10 := congrFun (congrFun hgg 1) 0
  have e11 := congrFun (congrFun hgg 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [det_fin_two] at hdet
  by_cases hs : g 0 0 + g 1 1 = 0
  · apply mul_ne_zero h2 hd0
    have hw : g 1 1 = -g 0 0 := by linear_combination hs
    rw [hw] at hdet
    linear_combination -e00 - hdet
  · have hy : g 0 1 = 0 := by
      have : g 0 1 * (g 0 0 + g 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hs
    have hz : g 1 0 = 0 := by
      have : g 1 0 * (g 0 0 + g 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hs
    apply hdsq (g 0 0)
    rw [sq]
    linear_combination e00 - g 1 0 * hy

theorem eq_one_or_neg_of_commute_typeII (h2 : (2 : K) ≠ 0) {d : K} (hd0 : d ≠ 0)
    (hdsq : ∀ l : K, l ^ 2 ≠ d) {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hMM : M * M = d • 1) (hμ : Mᵀ * formJ 2 K * M = d • formJ 2 K) (T : StatedSp 2 K)
    (hTT : ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1)
    (hTM : ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * M =
      M * ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) :
    ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 ∨
      ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1 := by
  by_contra hne
  push Not at hne
  obtain ⟨g, hg⟩ := exists_conj_T1 h2 T hTT hne.1 hne.2
  set G := ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hG
  set Gi := (((g⁻¹ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hGi
  set Tm := ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hTm
  have hGGi : G * Gi = 1 := by
    rw [hG, hGi, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
    rfl
  have hGiG : Gi * G = 1 := by
    rw [hG, hGi, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have hT1 : Gi * Tm * G = blk 1 (-1) := by
    have := congrArg (fun x : StatedSp 2 K => ((x : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hg
    simp only [Subgroup.coe_mul, Units.val_mul] at this
    rw [this, coe_T1]
  set M₁ := Gi * M * G with hM₁
  have hcomm : M₁ * blk 1 (-1) = blk 1 (-1) * M₁ := by
    rw [← hT1, hM₁]
    calc Gi * M * G * (Gi * Tm * G) = Gi * (M * Tm) * G := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc G Gi, hGGi, Matrix.one_mul]
      _ = Gi * (Tm * M) * G := by rw [hTM]
      _ = Gi * Tm * G * (Gi * M * G) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc G Gi, hGGi, Matrix.one_mul]
  obtain ⟨a, b, hab⟩ := exists_blk_of_commute h2 hcomm
  have hM₁sq : M₁ * M₁ = d • 1 := by
    rw [hM₁]
    calc Gi * M * G * (Gi * M * G) = Gi * (M * M) * G := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc G Gi, hGGi, Matrix.one_mul]
      _ = d • 1 := by rw [hMM, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hGiG]
  have hGs := symplectic_of_mem g
  have hGis := symplectic_of_mem g⁻¹
  have hM₁μ : M₁ᵀ * formJ 2 K * M₁ = d • formJ 2 K := by
    rw [hM₁]
    calc (Gi * M * G)ᵀ * formJ 2 K * (Gi * M * G) =
        Gᵀ * (Mᵀ * (Giᵀ * formJ 2 K * Gi) * M) * G := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = d • formJ 2 K := by
          rw [hGis, show Mᵀ * formJ 2 K * M = d • formJ 2 K from hμ, Matrix.mul_smul,
            Matrix.smul_mul, hGs]
  rw [hab] at hM₁sq hM₁μ
  rw [blk_mul, blk_eq_smul_one_iff] at hM₁sq
  rw [formJ_eq_blk, blk_transpose, blk_mul, blk_mul,
    show aᵀ * J₁ * a = a.det • J₁ from transpose_mul_J₁_mul a,
    show bᵀ * J₁ * b = b.det • J₁ from transpose_mul_J₁_mul b, ← blk_smul] at hM₁μ
  obtain ⟨h1, -⟩ := blk_injective _ _ _ _ hM₁μ
  have hdet : a.det = d := by
    have := congrFun (congrFun h1 0) 1
    simpa [J₁] using this
  exact false_of_sq_det h2 hd0 hdsq hM₁sq.1 hdet

@[expose] def b0 (d : K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks !![0, d; 1, 0] 0 0 !![0, 1; d, 0]

theorem b0_col_inl0 (d : K) : (fun s => b0 d s (Sum.inl 0)) = Pi.single (Sum.inl 1) 1 := by
  ext s
  rcases s with (s | s) <;> fin_cases s <;> simp [b0]

theorem b0_col_inl1 (d : K) : (fun s => b0 d s (Sum.inl 1)) = Pi.single (Sum.inl 0) d := by
  ext s
  rcases s with (s | s) <;> fin_cases s <;> simp [b0]

theorem b0_col_inr0 (d : K) : (fun s => b0 d s (Sum.inr 0)) = Pi.single (Sum.inr 1) d := by
  ext s
  rcases s with (s | s) <;> fin_cases s <;> simp [b0]

theorem b0_col_inr1 (d : K) : (fun s => b0 d s (Sum.inr 1)) = Pi.single (Sum.inr 0) 1 := by
  ext s
  rcases s with (s | s) <;> fin_cases s <;> simp [b0]

theorem exists_frame_typeII (h2 : (2 : K) ≠ 0) {d : K} (hd0 : d ≠ 0) (hdsq : ∀ l : K, l ^ 2 ≠ d)
    {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K} (hμ : Mᵀ * formJ 2 K * M = d • formJ 2 K)
    (hMM : M * M = d • 1) :
    ∃ g : StatedSp 2 K,
      M * ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * b0 d := by
  have hMM' : ∀ v, M *ᵥ (M *ᵥ v) = d • v := fun v => by
    rw [mulVec_mulVec, hMM, smul_mulVec, one_mulVec]
  have hsim := ωJ_similitude hμ
  have hself : ∀ x y, ωJ K (M *ᵥ x) y = ωJ K x (M *ᵥ y) := by
    intro x y
    have hy : y = M *ᵥ (d⁻¹ • M *ᵥ y) := by
      rw [mulVec_smul, hMM', smul_smul, inv_mul_cancel₀ hd0, one_smul]
    conv_lhs => rw [hy]
    rw [hsim, map_smul, smul_eq_mul]
    field_simp
  have halt : ∀ x, ωJ K x (M *ᵥ x) = 0 := by
    intro x
    have h1 := hself x x
    have h3 := ωJ_comm (K := K) (M *ᵥ x) x
    have h4 : (2 : K) * ωJ K x (M *ᵥ x) = 0 := by linear_combination -h1 + h3
    exact (mul_eq_zero.mp h4).resolve_left h2
  set e₁ : Fin 2 ⊕ Fin 2 → K := Pi.single (Sum.inl 0) 1 with he₁
  set f : Fin 2 ⊕ Fin 2 → K := Pi.single (Sum.inr 0) 1 with hf
  have hef : ωJ K e₁ f = 1 := by
    rw [ωJ_apply, he₁, hf]
    simp [formJ, Matrix.mulVec, dotProduct, Pi.single_apply]
  set b := ωJ K (M *ᵥ e₁) f with hb
  have hΔ : d - b ^ 2 ≠ 0 := fun h => hdsq b (by linear_combination -h)
  set Δ := d - b ^ 2 with hΔdef
  set f₁ := Δ⁻¹ • (d • f - b • M *ᵥ f) with hf₁
  set f₂ := Δ⁻¹ • (M *ᵥ f - b • f) with hf₂
  have p1 : ωJ K e₁ (M *ᵥ f) = b := by rw [← hself]
  have p2 : ωJ K (M *ᵥ e₁) (M *ᵥ f) = d := by rw [hsim, hef, mul_one]
  have pff : ωJ K f f = 0 := ωJ_self _
  have pfMf : ωJ K f (M *ᵥ f) = 0 := halt f
  have pMff : ωJ K (M *ᵥ f) f = 0 := by rw [ωJ_comm, pfMf, neg_zero]
  have pMfMf : ωJ K (M *ᵥ f) (M *ᵥ f) = 0 := ωJ_self _
  have e1f1 : ωJ K e₁ f₁ = 1 := by
    simp only [hf₁, map_smul, map_sub, smul_eq_mul, hef, p1]
    field_simp
    ring
  have e1f2 : ωJ K e₁ f₂ = 0 := by
    simp only [hf₂, map_smul, map_sub, smul_eq_mul, hef, p1]
    ring
  have e2f1 : ωJ K (M *ᵥ e₁) f₁ = 0 := by
    simp only [hf₁, map_smul, map_sub, smul_eq_mul, p2, ← hb]
    ring
  have e2f2 : ωJ K (M *ᵥ e₁) f₂ = 1 := by
    simp only [hf₂, map_smul, map_sub, smul_eq_mul, p2, ← hb]
    field_simp
    ring
  have hFF : ∀ x y : Fin 2 ⊕ Fin 2 → K, ∀ s t s' t' : K,
      ωJ K (s • f + t • M *ᵥ f) (s' • f + t' • M *ᵥ f) = 0 := by
    intro x y s t s' t'
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, pff,
      pfMf, pMff, pMfMf]
    ring
  have hf₁' : f₁ = (Δ⁻¹ * d) • f + (-(Δ⁻¹ * b)) • M *ᵥ f := by
    rw [hf₁, smul_sub, smul_smul, smul_smul, sub_eq_add_neg, neg_smul]
  have hf₂' : f₂ = (-(Δ⁻¹ * b)) • f + Δ⁻¹ • M *ᵥ f := by
    rw [hf₂, smul_sub, smul_smul, sub_eq_add_neg, neg_smul, add_comm]
  have f11 : ωJ K f₁ f₁ = 0 := by rw [hf₁']; exact hFF f f _ _ _ _
  have f12 : ωJ K f₁ f₂ = 0 := by rw [hf₁', hf₂']; exact hFF f f _ _ _ _
  have f21 : ωJ K f₂ f₁ = 0 := by rw [hf₁', hf₂']; exact hFF f f _ _ _ _
  have f22 : ωJ K f₂ f₂ = 0 := by rw [hf₂']; exact hFF f f _ _ _ _
  have e11 : ωJ K e₁ e₁ = 0 := ωJ_self _
  have e12 : ωJ K e₁ (M *ᵥ e₁) = 0 := halt e₁
  have e21 : ωJ K (M *ᵥ e₁) e₁ = 0 := by rw [ωJ_comm, e12, neg_zero]
  have e22 : ωJ K (M *ᵥ e₁) (M *ᵥ e₁) = 0 := ωJ_self _
  let E : Fin 2 → (Fin 2 ⊕ Fin 2 → K) := ![e₁, M *ᵥ e₁]
  let F : Fin 2 → (Fin 2 ⊕ Fin 2 → K) := ![f₁, f₂]
  have hsymp : (frameMat E F)ᵀ * formJ 2 K * frameMat E F = formJ 2 K := by
    refine frameMat_symplectic ?_ ?_ ?_ <;> intro i j <;> fin_cases i <;> fin_cases j <;>
      simp [E, F, e11, e12, e21, e22, f11, f12, f21, f22, e1f1, e1f2, e2f1, e2f2]
  refine ⟨toSp (frameMat E F) hsymp, ?_⟩
  rw [coe_toSp]
  apply mul_eq_of_mulVec_col
  intro k
  have hcol : ∀ k, (fun r => frameMat E F r k) = Sum.elim E F k := fun k => rfl
  rcases k with (k | k) <;> fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    rw [hcol]
  · rw [b0_col_inl0, mulVec_frameMat_single]
    simp [E]
  · rw [b0_col_inl1, mulVec_frameMat_single]
    simp [E, hMM']
  · rw [b0_col_inr0, mulVec_frameMat_single]
    simp only [F, Sum.elim_inr, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hf₁, hf₂, mulVec_smul, mulVec_sub, mulVec_smul, mulVec_smul, hMM']
    module
  · rw [b0_col_inr1, mulVec_frameMat_single]
    simp only [F, Sum.elim_inr, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul]
    rw [hf₁, hf₂, mulVec_smul, mulVec_sub, mulVec_smul, hMM']

theorem exists_conj_of_frames {X Y : gsp 2 K} {B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    {g g' : StatedSp 2 K}
    (hX : mat X * ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * B)
    (hY : mat Y * ((g' : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((g' : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * B) :
    ∃ n ∈ (conjAut 2 K).range, n⁻¹ * conjAut 2 K X * n = conjAut 2 K Y := by
  set G : gsp 2 K := ⟨g, statedSp_le_gsp g.2⟩ with hG
  set G' : gsp 2 K := ⟨g', statedSp_le_gsp g'.2⟩ with hG'
  refine ⟨conjAut 2 K (G * G'⁻¹), ⟨_, rfl⟩, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply gsp_ext
  have hX' : mat X * mat G = mat G * B := hX
  have hY' : mat Y * mat G' = mat G' * B := hY
  have hGi : mat G⁻¹ * mat X * mat G = B := by
    rw [Matrix.mul_assoc, hX', ← Matrix.mul_assoc, mat_inv_mul_mat, Matrix.one_mul]
  simp only [mat_mul, _root_.mul_inv_rev]
  calc mat G' * mat G⁻¹ * mat X * (mat G * mat G'⁻¹) =
      mat G' * (mat G⁻¹ * mat X * mat G) * mat G'⁻¹ := by simp only [Matrix.mul_assoc]
    _ = mat G' * B * mat G'⁻¹ := by rw [hGi]
    _ = mat Y := by
      rw [← hY', Matrix.mul_assoc, mat_mul_mat_inv, Matrix.mul_one]

theorem conjAut_smul [Finite K] (X : gsp 2 K) {l : K} (hl : l ≠ 0) {μ : Kˣ}
    (hX : (mat X)ᵀ * formJ 2 K * mat X = (μ : K) • formJ 2 K) :
    conjAut 2 K (gspOf (l • mat X) (Units.mk0 (l ^ 2) (pow_ne_zero 2 hl) * μ) (by
      rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, hX, smul_smul,
        smul_smul, Units.val_mul, Units.val_mk0]
      ring_nf)) = conjAut 2 K X :=
  conjAut_eq_of_smul _ _ (c := l) (by rw [coe_gspOf])

theorem exists_sq_mul_eq [Finite K] {μ d : K} (hμ0 : μ ≠ 0)
    (hd0 : d ≠ 0) (hμ : ∀ l : K, l ^ 2 ≠ μ) (hd : ∀ l : K, l ^ 2 ≠ d) :
    ∃ l : K, l ≠ 0 ∧ l ^ 2 * μ = d := by
  classical
  let _ := Fintype.ofFinite K
  have hsqμ : ¬ IsSquare μ := fun ⟨r, hr⟩ => hμ r (by rw [hr, sq])
  have hsqd : ¬ IsSquare d := fun ⟨r, hr⟩ => hd r (by rw [hr, sq])
  have cμ := quadraticChar_neg_one_iff_not_isSquare.mpr hsqμ
  have cd := quadraticChar_neg_one_iff_not_isSquare.mpr hsqd
  have cμi : quadraticChar K μ⁻¹ = -1 := by
    have h1 : quadraticChar K μ⁻¹ * quadraticChar K μ = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hμ0, map_one]
    rw [cμ] at h1
    linarith
  have c1 : quadraticChar K (d * μ⁻¹) = 1 := by
    rw [map_mul, cd, cμi]
    norm_num
  obtain ⟨r, hr⟩ := (quadraticChar_one_iff_isSquare (mul_ne_zero hd0 (inv_ne_zero hμ0))).mp c1
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact mul_ne_zero hd0 (inv_ne_zero hμ0) hr
  refine ⟨r, hr0, ?_⟩
  rw [sq, ← hr, mul_assoc, inv_mul_cancel₀ hμ0, mul_one]

end Cat7E6

end CFSG.ComponentClassification.GSThmB
