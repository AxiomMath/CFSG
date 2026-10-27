module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4Eich
public import CFSG.GH74.Generic.BProg.B2.GenLocU4Q2Frame

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.Assembly.LowTwoRank Subgroup Matrix
open GenLocU4Basic GenLocU4Gen GenLocU4Out GenLocU4Eich CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.ClassicalGroups.Unitary

namespace GenLocU4Q2

variable {K : Type} [Field K]

@[expose] def q2u (ι μ : K) : Fin 4 → K := ![1, ι, μ, μ * ι]
@[expose] def q2w (ι μ : K) : Fin 4 → K := ![1, -ι, -μ, μ * ι]
@[expose] def q2r (ι μ : K) : Fin 4 → K := ![1, -μ, ι, μ * ι]
@[expose] def q2r' (ι μ : K) : Fin 4 → K := ![1, μ, -ι, μ * ι]

end GenLocU4Q2

namespace GenLocU4Q2Core

open GenLocU4Q2

variable {K : Type} [Field K]

theorem q2_sum (ι μ : K) : q2u ι μ + q2w ι μ = q2r ι μ + q2r' ι μ := by
  funext i
  fin_cases i <;> simp [q2u, q2w, q2r, q2r']

theorem q2_sum_eq (ι μ : K) : q2u ι μ + q2w ι μ = (2 : K) • ![1, 0, 0, ι * μ] := by
  funext i
  fin_cases i <;> simp [q2u, q2w] <;> ring

section Herm

variable (σ : K ≃+* K) {ι μ : K}

theorem herm_uu (hι : ι * ι = -1) (hσι : σ ι = ι) : herm σ (q2u ι μ) (q2u ι μ) = 0 := by
  simp [herm, Fin.sum_univ_four, q2u, hσι]
  linear_combination (1 + σ μ * μ) * hι

theorem herm_ww (hι : ι * ι = -1) (hσι : σ ι = ι) : herm σ (q2w ι μ) (q2w ι μ) = 0 := by
  simp [herm, Fin.sum_univ_four, q2w, hσι]
  linear_combination (1 + σ μ * μ) * hι

theorem herm_rr (hι : ι * ι = -1) (hσι : σ ι = ι) : herm σ (q2r ι μ) (q2r ι μ) = 0 := by
  simp [herm, Fin.sum_univ_four, q2r, hσι]
  linear_combination (1 + σ μ * μ) * hι

theorem herm_r'r' (hι : ι * ι = -1) (hσι : σ ι = ι) : herm σ (q2r' ι μ) (q2r' ι μ) = 0 := by
  simp [herm, Fin.sum_univ_four, q2r', hσι]
  linear_combination (1 + σ μ * μ) * hι

theorem herm_uw (hσι : σ ι = ι) (hμ : σ μ * μ = 1) : herm σ (q2u ι μ) (q2w ι μ) = 0 := by
  simp [herm, Fin.sum_univ_four, q2u, q2w, hσι]
  linear_combination (-(1 - ι * ι)) * hμ

theorem herm_rr' (hσι : σ ι = ι) (hμ : σ μ * μ = 1) : herm σ (q2r ι μ) (q2r' ι μ) = 0 := by
  simp [herm, Fin.sum_univ_four, q2r, q2r', hσι]
  linear_combination (-(1 - ι * ι)) * hμ

theorem herm_ur (hι : ι * ι = -1) (hσι : σ ι = ι) (hμ : σ μ * μ = 1) :
    herm σ (q2u ι μ) (q2r ι μ) = ι * (σ μ - μ) := by
  simp [herm, Fin.sum_univ_four, q2u, q2r, hσι]
  linear_combination (σ μ * μ) * hι - hμ

end Herm

variable {ι μ : K}

theorem xi_u (hι : ι * ι = -1) : (xi : Matrix (Fin 4) (Fin 4) K) *ᵥ q2u ι μ = ι • q2u ι μ := by
  funext i
  fin_cases i <;> simp [xi, q2u, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
    first | ring1 | linear_combination (-1 : K) * hι | linear_combination (-μ) * hι

theorem xi_w (hι : ι * ι = -1) : (xi : Matrix (Fin 4) (Fin 4) K) *ᵥ q2w ι μ = (-ι) • q2w ι μ := by
  funext i
  fin_cases i <;> simp [xi, q2w, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
    first | ring1 | linear_combination (-1 : K) * hι | linear_combination (-μ) * hι | linear_combination μ * hι

theorem q2Y_r (hι : ι * ι = -1) : (q2Y : Matrix (Fin 4) (Fin 4) K) *ᵥ q2r ι μ = ι • q2r ι μ := by
  funext i
  fin_cases i <;> simp [q2Y, q2r, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
    first | ring1 | linear_combination (-1 : K) * hι | linear_combination (-μ) * hι

theorem q2Y_r' (hι : ι * ι = -1) : (q2Y : Matrix (Fin 4) (Fin 4) K) *ᵥ q2r' ι μ = (-ι) • q2r' ι μ := by
  funext i
  fin_cases i <;> simp [q2Y, q2r', Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
    first | ring1 | linear_combination (-1 : K) * hι | linear_combination (-μ) * hι | linear_combination μ * hι

@[expose] def mkSU4 {q : ℕ} (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnitaryU q M) (hdet : M.det = 1) :
    ↥(StatedSU 4 q K) :=
  ⟨⟨M, (M.map (· ^ q))ᵀ, mul_eq_one_comm.1 hM, hM⟩, Subgroup.subset_closure ⟨hdet, hM⟩⟩

theorem gM_mul {q : ℕ} (x y : ↥(StatedSU 4 q K)) : gM (x * y) = gM x * gM y := rfl

section Eich

variable [Finite K] {p f : ℕ}

theorem eich_in_Γ (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (Γ : Subgroup ↥(StatedSU 4 (p ^ f) K))
    (x : Matrix (Fin 4) (Fin 4) K) (hxU : (x.map (· ^ (p ^ f)))ᵀ * x = 1)
    (hxΓ : ∀ g : ↥(StatedSU 4 (p ^ f) K), gM g * x = x * gM g → g ∈ Γ) {ι : K} (hι : ι * ι = -1)
    (hιq : ι ^ (p ^ f) = ι) {u w : Fin 4 → K} (huu : hU (p ^ f) u u = 0) (hww : hU (p ^ f) w w = 0)
    (huw : hU (p ^ f) u w = 0) (hxu : x *ᵥ u = ι • u) (hxw : x *ᵥ w = (-ι) • w) (a : K)
    (ha : a ^ (p ^ f) = a) : ∃ g : ↥(StatedSU 4 (p ^ f) K), g ∈ Γ ∧ gM g = eichM (p ^ f) u w a := by
  obtain ⟨hU1, hdet⟩ := eichM_mem hp hp2 hK u w a ha huu hww huw
  exact ⟨mkSU4 _ hU1 hdet, hxΓ _ (eichM_comm_sq hp hK x u w a ι hι hιq hxU hxu hxw), rfl⟩

omit [Finite K] in
theorem tvM_two_smul {q : ℕ} (h2q : (2 : K) ^ q = 2) (v : Fin 4 → K) (c : K) :
    tvM q ((2 : K) • v) c = tvM q v (4 * c) := by
  unfold tvM
  congr 1
  ext i j
  simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mul_pow, h2q]
  ring

end Eich

@[expose] def xsM : Matrix (Fin 4) (Fin 4) K := !![0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, -1, 0, 0]

@[expose] def gmM : Matrix (Fin 4) (Fin 4) K := !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def pfM : Matrix (Fin 4) (Fin 4) K := !![1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 0, 1, 0, 0]

theorem xsM_det : (xsM : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  simp [xsM, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem gmM_det : (gmM : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  simp [gmM, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem xsM_unitary (σ : K ≃+* K) : ((xsM : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ * xsM = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xsM, Matrix.mul_apply, Fin.sum_univ_four]

theorem gmM_unitary (σ : K ≃+* K) : ((gmM : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ * gmM = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gmM, Matrix.mul_apply, Fin.sum_univ_four]

theorem pfM_unitary (σ : K ≃+* K) : ((pfM : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ * pfM = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pfM, Matrix.mul_apply, Fin.sum_univ_four]

theorem pfM_mul_transpose : (pfM : Matrix (Fin 4) (Fin 4) K) * (pfM : Matrix (Fin 4) (Fin 4) K)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pfM, Matrix.mul_apply, Fin.sum_univ_four]

theorem pfM_transpose_mul : (pfM : Matrix (Fin 4) (Fin 4) K)ᵀ * (pfM : Matrix (Fin 4) (Fin 4) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pfM, Matrix.mul_apply, Fin.sum_univ_four]

theorem xsM_comm_xi : (xsM : Matrix (Fin 4) (Fin 4) K) * xi = xi * xsM := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xsM, xi, Matrix.mul_apply, Fin.sum_univ_four]

theorem gmM_comm_xi : (gmM : Matrix (Fin 4) (Fin 4) K) * xi = xi * gmM := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gmM, xi, Matrix.mul_apply, Fin.sum_univ_four]

theorem xsM_act (b : K) : (xsM : Matrix (Fin 4) (Fin 4) K) *ᵥ ![1, 0, 0, b] = ![0, b, -1, 0] := by
  funext i
  fin_cases i <;> simp [xsM, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem gmM_act (b : K) : (gmM : Matrix (Fin 4) (Fin 4) K) *ᵥ ![1, 0, 0, b] = ![0, -1, 0, b] := by
  funext i
  fin_cases i <;> simp [gmM, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem pfM_act (w0 w1 w2 w3 : K) : (pfM : Matrix (Fin 4) (Fin 4) K) *ᵥ ![w0, w1, w2, w3] = ![w0, w2, w3, w1] := by
  funext i
  fin_cases i <;> simp [pfM, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

section Conj

variable (σ : K ≃+* K)

theorem conj_tvM {H : Matrix (Fin 4) (Fin 4) K} (hH : (H.map σ)ᵀ * H = 1)
    (v : Fin 4 → K) (c : K) :
    H * (1 + c • vecMulVec v (fun i => σ (v i))) * (H.map σ)ᵀ =
      1 + c • vecMulVec (H *ᵥ v) (fun i => σ ((H *ᵥ v) i)) := by
  have hHH : H * (H.map σ)ᵀ = 1 := mul_eq_one_comm.1 hH
  have hvec : (fun i => σ (v i)) ᵥ* (H.map σ)ᵀ = fun i => σ ((H *ᵥ v) i) := by
    funext j
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, mul_comm]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hHH, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, hvec]

end Conj

section Tv

variable [Finite K] {p f : ℕ}

theorem tv_mem_conj (hp : p.Prime) (hK : Nat.card K = (p ^ f) ^ 2) (Γ : Subgroup ↥(StatedSU 4 (p ^ f) K))
    (h : ↥(StatedSU 4 (p ^ f) K)) (hH : IsUnitaryU (p ^ f) (gM h)) (hh : h ∈ Γ) {v : Fin 4 → K}
    (hv : ∀ g, IsTransvU (p ^ f) v g → g ∈ Γ) : ∀ g, IsTransvU (p ^ f) (gM h *ᵥ v) g → g ∈ Γ := by
  intro g hg
  obtain ⟨c, hc, hc0, hgc⟩ := hg
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_sq hK
  have hf : (fun x : K => x ^ (p ^ f)) = ⇑(unitaryInvolution K p f) :=
    funext fun x => (unitaryInvolution_apply K p f x).symm
  have hinv := (isUnitaryInvolution_unitaryInvolution (K := K) (p := p) (f := f) hK).invol
  set σ := unitaryInvolution K p f with hσdef
  have hH' : ((gM h).map σ)ᵀ * gM h = 1 := by
    have := hH
    unfold IsUnitaryU at this
    rw [hf] at this
    exact this
  have hHinv : ((h⁻¹ : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) = ((h : GL (Fin 4) K))⁻¹ := rfl
  have hinvM : gM h⁻¹ = ((gM h).map σ)ᵀ := by
    show (((h : GL (Fin 4) K)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = _
    rw [Matrix.coe_units_inv]
    exact Matrix.inv_eq_left_inv hH'
  have hHs : (((gM h).map σ)ᵀ.map σ)ᵀ * ((gM h).map σ)ᵀ = 1 := by
    have e : (((gM h).map σ)ᵀ.map σ)ᵀ = gM h := by
      ext i j
      simp [hinv]
    rw [e]
    exact mul_eq_one_comm.1 hH'
  have e2 := conj_tvM σ hHs (gM h *ᵥ v) c
  have e3 : ((gM h).map σ)ᵀ *ᵥ (gM h *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hH', Matrix.one_mulVec]
  have e4 : (((gM h).map σ)ᵀ.map σ)ᵀ = gM h := by
    ext i j
    simp [hinv]
  rw [e3, e4] at e2
  have hg0 : h⁻¹ * g * h ∈ Γ := by
    apply hv
    refine ⟨c, hc, hc0, ?_⟩
    show gM h⁻¹ * gM g * gM h = _
    have hgc' : gM g = 1 + c • vecMulVec (gM h *ᵥ v) (fun i => ((gM h *ᵥ v) i) ^ (p ^ f)) := hgc
    rw [hinvM, hgc']
    have : (fun i => ((gM h *ᵥ v) i) ^ (p ^ f)) = fun i => σ ((gM h *ᵥ v) i) := by
      funext i; rw [hσdef, unitaryInvolution_apply]
    rw [this]
    have h5 : (fun i => (v i) ^ (p ^ f)) = fun i => σ (v i) := by
      funext i; rw [hσdef, unitaryInvolution_apply]
    rw [h5]
    exact e2
  have := Γ.mul_mem (Γ.mul_mem hh hg0) (Γ.inv_mem hh)
  simpa [mul_assoc] using this

omit [Finite K] in
theorem isTransvU_smul {q : ℕ} (hqq : ∀ x : K, (x ^ q) ^ q = x) {lam : K} (hlam : lam ≠ 0) {w : Fin 4 → K}
    {g : ↥(StatedSU 4 q K)} (hg : IsTransvU q w g) : IsTransvU q (lam • w) g := by
  obtain ⟨c, hc, hc0, hgc⟩ := hg
  have hl : lam ^ q ≠ 0 := pow_ne_zero q hlam
  refine ⟨c / (lam ^ q * lam), ?_, div_ne_zero hc0 (mul_ne_zero hl hlam), ?_⟩
  · rw [div_pow, mul_pow, hqq lam]
    have hcq : c ^ q = -c := by linear_combination hc
    rw [hcq]
    field_simp
    ring
  · rw [hgc]
    congr 1
    ext i j
    simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mul_pow]
    field_simp

end Tv

end GenLocU4Q2Core

namespace GenLocU4Q2

open GenLocU4Q2Core

variable {K : Type} [Field K] [Finite K] {p f : ℕ}

theorem q2_tv_mem (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (_hq : p ^ f % 4 = 1)
    (Γ : Subgroup ↥(StatedSU 4 (p ^ f) K))
    (hx : ∀ g : ↥(StatedSU 4 (p ^ f) K), gM g * xi = xi * gM g → g ∈ Γ)
    (hy : ∀ g : ↥(StatedSU 4 (p ^ f) K), gM g * q2Y = q2Y * gM g → g ∈ Γ)
    {ι μ : K} (hι : ι * ι = -1) (hιq : ι ^ (p ^ f) = ι) (hμ : μ ^ (p ^ f) * μ = 1) (hμ2 : μ * μ ≠ 1) :
    ∀ g, IsTransvU (p ^ f) ![1, 0, 0, ι * μ] g → g ∈ Γ := by
  intro g hg
  obtain ⟨c, hc, hc0, hgc⟩ := hg
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_sq hK
  have hσq : ∀ x : K, unitaryInvolution K p f x = x ^ (p ^ f) := unitaryInvolution_apply K p f
  set σ := unitaryInvolution K p f with hσdef
  have hinv := (isUnitaryInvolution_unitaryInvolution (K := K) (p := p) (f := f) hK).invol
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rwa [ringChar.eq K p])
  have hσι : σ ι = ι := by rw [hσq]; exact hιq
  have hσμ : σ μ * μ = 1 := by rw [hσq]; exact hμ
  have hf : (fun x : K => x ^ (p ^ f)) = ⇑σ := funext fun x => (hσq x).symm
  have h2q : (2 : K) ^ (p ^ f) = 2 := by rw [← hσq]; exact map_ofNat σ 2
  have huu : hU (p ^ f) (q2u ι μ) (q2u ι μ) = 0 := by rw [hU_eq]; exact herm_uu σ hι hσι
  have hww : hU (p ^ f) (q2w ι μ) (q2w ι μ) = 0 := by rw [hU_eq]; exact herm_ww σ hι hσι
  have hrr : hU (p ^ f) (q2r ι μ) (q2r ι μ) = 0 := by rw [hU_eq]; exact herm_rr σ hι hσι
  have hr'r' : hU (p ^ f) (q2r' ι μ) (q2r' ι μ) = 0 := by rw [hU_eq]; exact herm_r'r' σ hι hσι
  have huw : hU (p ^ f) (q2u ι μ) (q2w ι μ) = 0 := by rw [hU_eq]; exact herm_uw σ hσι hσμ
  have hrr' : hU (p ^ f) (q2r ι μ) (q2r' ι μ) = 0 := by rw [hU_eq]; exact herm_rr' σ hσι hσμ
  have hxiU : ((xi : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * xi = 1 := by
    rw [hf]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [xi, Matrix.mul_apply, Fin.sum_univ_four]
  have hq2U : ((q2Y : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * q2Y = 1 := by
    rw [hf]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [q2Y, Matrix.mul_apply, Fin.sum_univ_four]
  have hι0 : ι ≠ 0 := by
    rintro rfl
    simp at hι
  have hδ : σ μ - μ ≠ 0 := by
    intro h
    apply hμ2
    have h' : σ μ = μ := by linear_combination h
    rw [h'] at hσμ
    exact hσμ
  have hδ' : μ - σ μ ≠ 0 := by
    intro h
    apply hδ
    linear_combination -h
  have h8 : (8 : K) ≠ 0 := by
    have : (8 : K) = 2 * 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero (mul_ne_zero h2 h2) h2
  have hσc : σ c = -c := by
    rw [hσq]
    linear_combination hc
  set a : K := -c / (8 * ι * (σ μ - μ)) with ha_def
  have ha : a ^ (p ^ f) = a := by
    rw [← hσq, ha_def, map_div₀, map_neg, map_mul, map_mul, map_sub, hσc, hσι, hinv, map_ofNat]
    field_simp
    ring
  have hna : (-a) ^ (p ^ f) = -a := by rw [← hσq, map_neg, hσq, ha]
  obtain ⟨g1, hg1, hg1M⟩ := eich_in_Γ hp hp2 hK Γ xi hxiU hx hι hιq huu hww huw (xi_u hι) (xi_w hι) a ha
  obtain ⟨g3, hg3, hg3M⟩ := eich_in_Γ hp hp2 hK Γ xi hxiU hx hι hιq huu hww huw (xi_u hι) (xi_w hι) (-a) hna
  obtain ⟨g2, hg2, hg2M⟩ := eich_in_Γ hp hp2 hK Γ q2Y hq2U hy hι hιq hrr hr'r' hrr' (q2Y_r hι) (q2Y_r' hι)
    1 (by simp)
  obtain ⟨g4, hg4, hg4M⟩ := eich_in_Γ hp hp2 hK Γ q2Y hq2U hy hι hιq hrr hr'r' hrr' (q2Y_r hι) (q2Y_r' hι)
    (-1) (by rw [← hσq, map_neg, map_one])
  have hprod : g1 * g2 * g3 * g4 ∈ Γ := Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hg1 hg2) hg3) hg4
  have hE1 := eich_comm hp hK (q2u ι μ) (q2w ι μ) (q2r ι μ) (q2r' ι μ) a 1 ha (by simp) huu hww hrr hr'r' huw hrr'
    (q2_sum ι μ)
  have hmat : gM (g1 * g2 * g3 * g4) = tvM (p ^ f) (q2u ι μ + q2w ι μ)
      (-(a * 1 * (hU (p ^ f) (q2u ι μ) (q2r ι μ) - (hU (p ^ f) (q2u ι μ) (q2r ι μ)) ^ (p ^ f)))) := by
    rw [← hE1, gM_mul, gM_mul, gM_mul, hg1M, hg2M, hg3M, hg4M]
  have hγ : hU (p ^ f) (q2u ι μ) (q2r ι μ) = ι * (σ μ - μ) := by
    rw [hU_eq]
    exact herm_ur σ hι hσι hσμ
  have hγq : (ι * (σ μ - μ)) ^ (p ^ f) = -(ι * (σ μ - μ)) := by
    rw [← hσq, map_mul, map_sub, hσι, hinv]
    ring
  have hc4 : 4 * (-(a * 1 * (ι * (σ μ - μ) - -(ι * (σ μ - μ))))) = c := by
    rw [ha_def]
    field_simp
    ring
  rw [hγ, hγq, q2_sum_eq, tvM_two_smul h2q, hc4] at hmat
  have hgeq : g = g1 * g2 * g3 * g4 := by
    apply Subtype.ext
    apply Units.ext
    show gM g = gM (g1 * g2 * g3 * g4)
    rw [hmat]
    exact hgc
  rw [hgeq]
  exact hprod

theorem q2_core (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    (Γ : Subgroup ↥(StatedSU 4 (p ^ f) K))
    (hx : ∀ g : ↥(StatedSU 4 (p ^ f) K), gM g * xi = xi * gM g → g ∈ Γ)
    (hy : ∀ g : ↥(StatedSU 4 (p ^ f) K), gM g * q2Y = q2Y * gM g → g ∈ Γ) : Γ = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_sq hK
  have hσq : ∀ x : K, unitaryInvolution K p f x = x ^ (p ^ f) := unitaryInvolution_apply K p f
  have hinv := (isUnitaryInvolution_unitaryInvolution (K := K) (p := p) (f := f) hK).invol
  set σ := unitaryInvolution K p f with hσdef
  have hf : (fun x : K => x ^ (p ^ f)) = ⇑σ := funext fun x => (hσq x).symm
  have hqq : ∀ x : K, (x ^ (p ^ f)) ^ (p ^ f) = x := fun x => by rw [← hσq, ← hσq]; exact hinv x
  have hge : 1 < p ^ f := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK] at h1
    by_contra hle
    have : p ^ f ≤ 1 := not_lt.mp hle
    nlinarith [Nat.zero_le (p ^ f)]
  have h3 : 3 ≤ p ^ f := by omega
  obtain ⟨ι, hι⟩ : ∃ ι : K, ι * ι = -1 := by
    have := Fintype.ofFinite K
    have h4 : Fintype.card K % 4 ≠ 3 := by
      rw [← Nat.card_eq_fintype_card, hK, Nat.pow_mod, hq]
      norm_num
    obtain ⟨r, hr⟩ := FiniteField.isSquare_neg_one_iff.2 h4
    exact ⟨r, hr.symm⟩
  have hιq : ι ^ (p ^ f) = ι := by
    obtain ⟨k, hk⟩ : ∃ k, p ^ f = 4 * k + 1 := ⟨p ^ f / 4, by omega⟩
    rw [hk, pow_succ, pow_mul]
    have h4 : ι ^ 4 = 1 := by linear_combination (ι * ι - 1) * hι
    rw [h4, one_pow, one_mul]
  obtain ⟨μ, hμ, hμ2⟩ := GenLocU4Gen.exists_unit_scalar_sq_ne_one hK h3
  have hβ : (ι * μ) ^ (p ^ f) * (ι * μ) = -1 := by
    rw [mul_pow, hιq]
    linear_combination (μ ^ (p ^ f) * μ) * hι - hμ
  have hβσ : σ (ι * μ) * (ι * μ) = -1 := by rw [hσq]; exact hβ
  have hβ0 : ι * μ ≠ 0 := by
    intro h
    rw [h] at hβ
    simp at hβ
  have T1 := q2_tv_mem hp hp2 hK hq Γ hx hy hι hιq hμ hμ2
  have hμ' : (-μ) ^ (p ^ f) * (-μ) = 1 := by
    rw [← hσq, map_neg, hσq]
    linear_combination hμ
  have T2 := q2_tv_mem hp hp2 hK hq Γ hx hy hι hιq hμ' (by simpa using hμ2)
  have hxsU : IsUnitaryU (p ^ f) (xsM : Matrix (Fin 4) (Fin 4) K) := by
    unfold IsUnitaryU
    rw [hf]
    exact xsM_unitary σ
  have hgmU : IsUnitaryU (p ^ f) (gmM : Matrix (Fin 4) (Fin 4) K) := by
    unfold IsUnitaryU
    rw [hf]
    exact gmM_unitary σ
  let xs : ↥(StatedSU 4 (p ^ f) K) := mkSU4 xsM hxsU xsM_det
  let gm : ↥(StatedSU 4 (p ^ f) K) := mkSU4 gmM hgmU gmM_det
  have hxsM : gM xs = xsM := rfl
  have hgmM : gM gm = gmM := rfl
  have hxs : xs ∈ Γ := hx _ xsM_comm_xi
  have hgm : gm ∈ Γ := hx _ gmM_comm_xi
  have T3 : ∀ g, IsTransvU (p ^ f) ![0, ι * μ, -1, 0] g → g ∈ Γ := by
    intro g hg
    refine tv_mem_conj hp hK Γ xs (by rw [hxsM]; exact hxsU) hxs T1 g ?_
    rw [hxsM, xsM_act]
    exact hg
  have T4 : ∀ g, IsTransvU (p ^ f) ![0, -(ι * μ), -1, 0] g → g ∈ Γ := by
    intro g hg
    refine tv_mem_conj hp hK Γ xs (by rw [hxsM]; exact hxsU) hxs T2 g ?_
    rw [hxsM, xsM_act, mul_neg]
    exact hg
  have T5 : ∀ g, IsTransvU (p ^ f) ![0, -1, 0, ι * μ] g → g ∈ Γ := by
    intro g hg
    refine tv_mem_conj hp hK Γ gm (by rw [hgmM]; exact hgmU) hgm T1 g ?_
    rw [hgmM, gmM_act]
    exact hg
  have T2' : ∀ g, IsTransvU (p ^ f) ![1, 0, 0, -(ι * μ)] g → g ∈ Γ := by
    intro g hg
    apply T2 g
    rw [mul_neg]
    exact hg
  have hγ : ((ι * μ) ^ (p ^ f)) ^ (p ^ f) * (ι * μ) ^ (p ^ f) = -1 := by
    rw [hqq]
    linear_combination hβ
  have hβγ : (ι * μ) * (ι * μ) ^ (p ^ f) = -1 := by linear_combination hβ
  let PG : GL (Fin 4) K := ⟨pfM, (pfM : Matrix (Fin 4) (Fin 4) K)ᵀ, pfM_mul_transpose, pfM_transpose_mul⟩
  have hPG : (PG : Matrix (Fin 4) (Fin 4) K) = pfM := rfl
  have hPU : IsUnitaryU (p ^ f) (PG : Matrix (Fin 4) (Fin 4) K) := by
    rw [hPG]
    unfold IsUnitaryU
    rw [hf]
    exact pfM_unitary σ
  refine su4_eq_top_of_tv_frame hp hp2 hK Γ PG hPU (ι * μ) ((ι * μ) ^ (p ^ f)) hβ hγ ?_
    ![0, ι * μ, -1, 0] ?_ ?_ ?_
  · intro w hw g hg
    rcases hw with rfl | rfl | rfl | rfl
    · rw [hPG, pfM_act] at hg
      exact T1 g hg
    · rw [hPG, pfM_act] at hg
      exact T2' g hg
    · rw [hPG, pfM_act] at hg
      have hg' := isTransvU_smul hqq hβ0 hg
      have e : (ι * μ) • (![0, 1, (ι * μ) ^ (p ^ f), 0] : Fin 4 → K) = ![0, ι * μ, -1, 0] := by
        funext i
        fin_cases i <;> simp [hβγ]
      rw [e] at hg'
      exact T3 g hg'
    · rw [hPG, pfM_act] at hg
      have hg' := isTransvU_smul hqq (neg_ne_zero.2 hβ0) hg
      have e : (-(ι * μ)) • (![0, 1, -(ι * μ) ^ (p ^ f), 0] : Fin 4 → K) = ![0, -(ι * μ), -1, 0] := by
        funext i
        fin_cases i <;> simp
        linear_combination hβγ
      rw [e] at hg'
      exact T4 g hg'
  · simp only [Fin.sum_univ_four]
    simp [← hσq]
    rw [map_mul] at hβσ
    linear_combination hβσ
  · show (0 : K) ^ (p ^ f) * 0 + (ι * μ) ^ (p ^ f) * (ι * μ) ≠ 0
    rw [hβ, mul_zero, zero_add]
    exact neg_ne_zero.2 one_ne_zero
  · intro g hg
    rw [hPG, pfM_act] at hg
    exact T5 g hg

end GenLocU4Q2

end CFSG.GH74.Generic.BProg.B2
