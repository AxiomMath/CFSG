module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2LWit

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {K : Type} [Field K]

theorem exists_dotProduct_of_notMem {W : Submodule K (Fin n → K)} {v : Fin n → K}
    (hv : v ∉ W) : ∃ χ : Fin n → K, χ ⬝ᵥ v = 1 ∧ ∀ w ∈ W, χ ⬝ᵥ w = 0 := by
  obtain ⟨f, hf, hW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  have key : ∀ w : Fin n → K, f w = (fun j => f (Pi.single j 1)) ⬝ᵥ w := by
    intro w
    conv_lhs => rw [← Finset.univ_sum_single w]
    rw [map_sum, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (Pi.single j (w j) : Fin n → K) = w j • Pi.single j 1 by
      ext k; by_cases hk : k = j <;> simp [hk], map_smul, smul_eq_mul, mul_comm]
  refine ⟨(f v)⁻¹ • fun j => f (Pi.single j 1), ?_, fun w hw => ?_⟩
  · rw [smul_dotProduct, ← key, smul_eq_mul, inv_mul_cancel₀ hf]
  · have h0 : f w = 0 := by
      have : f w ∈ W.map f := Submodule.mem_map_of_mem hw
      rwa [hW, Submodule.mem_bot] at this
    rw [smul_dotProduct, ← key, h0, smul_zero]

theorem vecMul_eq_zero_of {N : Matrix (Fin n) (Fin n) K} {χ : Fin n → K}
    (h : ∀ f, χ ⬝ᵥ (N *ᵥ f) = 0) : χ ᵥ* N = 0 := by
  ext j
  have := h (Pi.single j 1)
  rw [dotProduct_mulVec, dotProduct_single, mul_one] at this
  exact this

theorem conjAut_proj_eq_of_comm {A : GL (Fin n) K} {μ : K} {g : SpecialLinearGroup (Fin n) K}
    (hg : (g : Matrix (Fin n) (Fin n) K) * ((A : Matrix (Fin n) (Fin n) K) + μ • 1) =
      ((A : Matrix (Fin n) (Fin n) K) + μ • 1) * g) :
    conjAut n K A (proj n K g) = proj n K g := by
  rw [conjAut_proj]
  congr 1
  ext i j
  rw [coe_slConjugation]
  have hgA : (g : Matrix (Fin n) (Fin n) K) * A = A * g := by
    rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul] at hg
    exact add_right_cancel hg
  rw [← hgA, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

@[expose] def dbl (N : Matrix (Fin n) (Fin n) K) (f χ : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  vecMulVec (N *ᵥ f) χ + vecMulVec f (χ ᵥ* N)

variable {N : Matrix (Fin n) (Fin n) K}

theorem dbl_comm (hN : N * N = 0) (f χ : Fin n → K) : N * dbl N f χ = dbl N f χ * N := by
  rw [dbl, mul_add, add_mul, mul_vecMulVec, mul_vecMulVec, vecMulVec_mul, vecMulVec_mul,
    mulVec_mulVec, hN, zero_mulVec, vecMul_vecMul, hN, vecMul_zero]
  ext i j
  simp [vecMulVec_apply, add_comm]

theorem dbl_mul_dbl (hN : N * N = 0) {f g χ ψ : Fin n → K} (h0 : χ ⬝ᵥ g = 0) :
    dbl N f χ * dbl N g ψ = (χ ⬝ᵥ (N *ᵥ g)) • dbl N f ψ := by
  have e1 : (χ ᵥ* N) ⬝ᵥ (N *ᵥ g) = 0 := by
    rw [dotProduct_mulVec, vecMul_vecMul, hN, vecMul_zero, zero_dotProduct]
  have e2 : (χ ᵥ* N) ⬝ᵥ g = χ ⬝ᵥ (N *ᵥ g) := (dotProduct_mulVec _ _ _).symm
  rw [dbl, dbl, add_mul, mul_add, mul_add, vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec,
    vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec, e1, e2, h0, zero_smul, zero_smul,
    vecMulVec_zero, vecMulVec_zero, add_zero, zero_add, vecMulVec_smul, vecMulVec_smul, dbl,
    smul_add]

theorem dbl_mulVec (hN : N * N = 0) (f χ g : Fin n → K) :
    dbl N f χ *ᵥ (N *ᵥ g) = (χ ⬝ᵥ (N *ᵥ g)) • (N *ᵥ f) := by
  rw [dbl, add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, dotProduct_mulVec (χ ᵥ* N),
    vecMul_vecMul, hN, vecMul_zero, zero_dotProduct, MulOpposite.op_zero, zero_smul, add_zero,
    op_smul_eq_smul]

theorem vecMulVec_mul_mul_eq_zero {G : Matrix (Fin n) (Fin n) K} (hG : G * N = N * G)
    {f ψ : Fin n → K} (hψ : ψ ᵥ* N = 0) :
    vecMulVec (N *ᵥ f) ψ * G * vecMulVec (N *ᵥ f) ψ = 0 := by
  rw [vecMulVec_mul, vecMulVec_mul_vecMulVec, ← dotProduct_mulVec, mulVec_mulVec, hG,
    ← mulVec_mulVec, dotProduct_mulVec, hψ, zero_dotProduct, zero_smul, vecMulVec_zero]

theorem inv_comm_of_comm {g : SpecialLinearGroup (Fin n) K}
    (hg : (g : Matrix (Fin n) (Fin n) K) * N = N * g) :
    ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * N =
      N * (g⁻¹ : SpecialLinearGroup (Fin n) K) := by
  have h1 : ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * g = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h2 : (g : Matrix (Fin n) (Fin n) K) * (g⁻¹ : SpecialLinearGroup (Fin n) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  set G' := ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
  calc G' * N = G' * N * ((g : Matrix (Fin n) (Fin n) K) * G') := by rw [h2, mul_one]
    _ = G' * (N * g) * G' := by simp only [mul_assoc]
    _ = G' * (g * N) * G' := by rw [hg]
    _ = (G' * g) * N * G' := by simp only [mul_assoc]
    _ = N * G' := by rw [h1, one_mul]

theorem vec_add_self (h2 : (2 : K) = 0) (x : Fin n → K) : x + x = 0 := by
  ext i
  rw [Pi.add_apply, ← two_mul, h2, zero_mul, Pi.zero_apply]

theorem one_add_comm {X : Matrix (Fin n) (Fin n) K} (h : N * X = X * N) :
    N * (1 + X) = (1 + X) * N := by
  rw [mul_add, add_mul, h, mul_one, one_mul]

theorem hasWit_of_rank_two (h2 : (2 : K) = 0) {A : GL (Fin n) K} {μ : K}
    (hNA : N = (A : Matrix (Fin n) (Fin n) K) + μ • 1) (hN : N * N = 0) {f₁ f₂ : Fin n → K}
    (hind : LinearIndependent K ![N *ᵥ f₁, N *ᵥ f₂]) : HasWit (conjAut n K A) := by
  have hpair := LinearIndependent.pair_iff.mp hind
  have hNN : ∀ z, N *ᵥ (N *ᵥ z) = 0 := fun z => by rw [mulVec_mulVec, hN, zero_mulVec]
  have hm : ∀ {g₁ g₂ : Fin n → K}, (∀ s t : K, s • (N *ᵥ g₁) + t • (N *ᵥ g₂) = 0 → s = 0 ∧ t = 0) →
      N *ᵥ g₁ ∉ Submodule.span K {N *ᵥ g₂, f₁, f₂} := by
    intro g₁ g₂ hp hmem
    rw [Submodule.mem_span_insert] at hmem
    obtain ⟨a, z, hz, hza⟩ := hmem
    rw [Submodule.mem_span_pair] at hz
    obtain ⟨b, c, rfl⟩ := hz
    have h0 : b • (N *ᵥ f₁) + c • (N *ᵥ f₂) = 0 := by
      have := congrArg (N *ᵥ ·) hza
      simp only [mulVec_add, mulVec_smul, hNN, smul_zero, zero_add] at this
      exact this.symm
    have hb := hpair b c h0
    rw [hb.1, hb.2, zero_smul, zero_smul, add_zero, add_zero] at hza
    have := hp 1 (-a) (by rw [hza, one_smul, neg_smul, add_neg_cancel])
    exact one_ne_zero this.1
  have hp12 : ∀ s t : K, s • (N *ᵥ f₁) + t • (N *ᵥ f₂) = 0 → s = 0 ∧ t = 0 := hpair
  have hp21 : ∀ s t : K, s • (N *ᵥ f₂) + t • (N *ᵥ f₁) = 0 → s = 0 ∧ t = 0 := fun s t h =>
    (hpair t s (by rw [add_comm]; exact h)).symm
  obtain ⟨χ₁, h11, h1W⟩ := exists_dotProduct_of_notMem (hm hp12)
  obtain ⟨χ₂, h22, h2W⟩ := exists_dotProduct_of_notMem (hm hp21)
  have h12 : χ₁ ⬝ᵥ (N *ᵥ f₂) = 0 := h1W _ (Submodule.subset_span (by simp))
  have h1f₁ : χ₁ ⬝ᵥ f₁ = 0 := h1W _ (Submodule.subset_span (by simp))
  have h1f₂ : χ₁ ⬝ᵥ f₂ = 0 := h1W _ (Submodule.subset_span (by simp))
  have h21 : χ₂ ⬝ᵥ (N *ᵥ f₁) = 0 := h2W _ (Submodule.subset_span (by simp))
  have h2f₁ : χ₂ ⬝ᵥ f₁ = 0 := h2W _ (Submodule.subset_span (by simp))
  have h2f₂ : χ₂ ⬝ᵥ f₂ = 0 := h2W _ (Submodule.subset_span (by simp))
  have hf₁ : f₁ ∉ LinearMap.range N.mulVecLin ⊔ Submodule.span K {f₂} := by
    intro hmem
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have := congrArg (N *ᵥ ·) hyz
    simp only [mulVecLin_apply, mulVec_add, mulVec_smul, hNN, zero_add] at this
    have := hpair 1 (-c) (by rw [← this, one_smul, neg_smul, add_neg_cancel])
    exact one_ne_zero this.1
  obtain ⟨ψ, hψ1, hψW⟩ := exists_dotProduct_of_notMem hf₁
  have hψN : ψ ᵥ* N = 0 := vecMul_eq_zero_of fun f =>
    hψW _ (Submodule.mem_sup_left (LinearMap.mem_range.mpr ⟨f, rfl⟩))
  set a := dbl N f₁ χ₂ with ha
  set b := dbl N f₂ χ₁ with hb
  have haa : a * a = 0 := by rw [ha, dbl_mul_dbl hN h2f₁, h21, zero_smul]
  have hbb : b * b = 0 := by rw [hb, dbl_mul_dbl hN h1f₂, h12, zero_smul]
  have hab : a * b = dbl N f₁ χ₁ := by rw [ha, hb, dbl_mul_dbl hN h2f₂, h22, one_smul]
  have hba : b * a = dbl N f₂ χ₂ := by rw [ha, hb, dbl_mul_dbl hN h1f₁, h11, one_smul]
  have haba : a * b * a = a := by rw [hab, ha, dbl_mul_dbl hN h1f₁, h11, one_smul]
  have hbab : b * a * b = b := by rw [hba, hb, dbl_mul_dbl hN h2f₂, h22, one_smul]
  set h := unipOf h2 a haa * unipOf h2 b hbb with hh
  have hH : (h : Matrix (Fin n) (Fin n) K) = (1 + a) * (1 + b) := by
    rw [hh, Matrix.SpecialLinearGroup.coe_mul, coe_unipOf, coe_unipOf]
  have h3 : h ^ 3 = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, hH,
      pow_three_of_rel (add_self_eq_zero_of_two h2) haa hbb haba hbab]
    rfl
  have hcomm : (h : Matrix (Fin n) (Fin n) K) * N = N * h := by
    rw [hH, mul_assoc, ← one_add_comm (dbl_comm hN f₂ χ₁), ← mul_assoc,
      ← one_add_comm (dbl_comm hN f₁ χ₂), mul_assoc]
  set E := vecMulVec (N *ᵥ f₁) ψ with hE
  have hψe : ψ ⬝ᵥ (N *ᵥ f₁) = 0 := by rw [dotProduct_mulVec, hψN, zero_dotProduct]
  have hEE : E * E = 0 := by
    rw [hE, vecMulVec_mul_vecMulVec, hψe, zero_smul, vecMulVec_zero]
  have hEcomm : (1 + E) * N = N * (1 + E) := by
    rw [mul_add, add_mul, mul_one, one_mul, hE, vecMulVec_mul, hψN, vecMulVec_zero,
      mul_vecMulVec, hNN, zero_vecMulVec]
  have hNA' : ∀ g : SpecialLinearGroup (Fin n) K, (g : Matrix (Fin n) (Fin n) K) * N = N * g →
      conjAut n K A (proj n K g) = proj n K g := fun g hg =>
    conjAut_proj_eq_of_comm (by rw [← hNA]; exact hg)
  have hae₁ : a *ᵥ (N *ᵥ f₁) = 0 := by rw [ha, dbl_mulVec hN, h21, zero_smul]
  have hae₂ : a *ᵥ (N *ᵥ f₂) = N *ᵥ f₁ := by rw [ha, dbl_mulVec hN, h22, one_smul]
  have hbe₁ : b *ᵥ (N *ᵥ f₁) = N *ᵥ f₂ := by rw [hb, dbl_mulVec hN, h11, one_smul]
  have hHe : (h : Matrix (Fin n) (Fin n) K) *ᵥ (N *ᵥ f₁) = N *ᵥ f₂ := by
    have h1 : (1 + b) *ᵥ (N *ᵥ f₁) = N *ᵥ f₁ + N *ᵥ f₂ := by
      rw [add_mulVec, one_mulVec, hbe₁]
    rw [hH, ← mulVec_mulVec, h1, add_mulVec, one_mulVec, mulVec_add, hae₁, hae₂, zero_add,
      show N *ᵥ f₁ + N *ᵥ f₂ + N *ᵥ f₁ = N *ᵥ f₂ + (N *ᵥ f₁ + N *ᵥ f₁) by abel,
      vec_add_self h2, add_zero]
  have hne : (h : Matrix (Fin n) (Fin n) K) * E ≠ E * h := by
    intro heq
    have := congrArg (· *ᵥ f₁) heq
    simp only [← mulVec_mulVec, hE, vecMulVec_mulVec, hψ1, op_smul_eq_smul, one_smul, hHe] at this
    have := hpair (-(ψ ⬝ᵥ ((h : Matrix (Fin n) (Fin n) K) *ᵥ f₁))) 1
      (by rw [one_smul, this, neg_smul, neg_add_cancel])
    exact one_ne_zero this.2
  refine hasWit_of_sl h2 h (m := 3) ⟨1, rfl⟩ h3 hEE
    (vecMulVec_mul_mul_eq_zero hcomm hψN) (vecMulVec_mul_mul_eq_zero (inv_comm_of_comm hcomm) hψN)
    hne (hNA' h hcomm) (hNA' _ ?_)
  rw [coe_unipOf]
  exact hEcomm

end CFSG.ComponentClassification.HarrisLit.L33.C2
