module

public import CFSG.LieType.SeitzGeneration.HeisTorusIsolate
public import CFSG.LieType.SeitzGeneration.HeisTorusIdent

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix

variable {F : Type*} [Field F] {p : ℕ}

theorem caseA_pow_neg {ζ : F} (hζ : ζ ^ p = 1) (j : Fin p) :
    ζ ^ ((-j : Fin p) : ℕ) = (ζ ^ (j : ℕ))⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [Fin.val_neg', ← pow_eq_pow_mod _ hζ, ← pow_add, Nat.sub_add_cancel j.isLt.le, hζ]

theorem caseA_pow_mul_neg {ζ : F} (hζ : ζ ^ p = 1) (a k : Fin p) :
    ζ ^ ((a : ℕ) * ((-k : Fin p) : ℕ)) = (ζ ^ ((a : ℕ) * (k : ℕ)))⁻¹ := by
  rw [mul_comm, pow_mul, caseA_pow_neg hζ, inv_pow, ← pow_mul, mul_comm]

theorem caseA_pow_neg_mul {ζ : F} (hζ : ζ ^ p = 1) (a k : Fin p) :
    ζ ^ (((-k : Fin p) : ℕ) * (a : ℕ)) = (ζ ^ ((k : ℕ) * (a : ℕ)))⁻¹ := by
  rw [pow_mul, caseA_pow_neg hζ, inv_pow, ← pow_mul]

theorem caseA_transpose_conj (hp : 2 ≤ p) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (t : Fin p → F) :
    (heisFourierMat ζ * diagonal t * (heisFourierMat ζ)⁻¹)ᵀ =
      heisFourierMat ζ * diagonal (fun k => t (-k)) * (heisFourierMat ζ)⁻¹ := by
  rw [heisFourierMat_inv hζ hp]
  ext a b
  rw [transpose_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.of_apply, heisFourierMat]
  rw [← Equiv.sum_comp (Equiv.neg (Fin p))]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Equiv.neg_apply, neg_neg, caseA_pow_mul_neg hζ.pow_eq_one,
    caseA_pow_neg_mul hζ.pow_eq_one, inv_inv]
  ring_nf

theorem caseA_exists_mem_fourier {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {K : Subgroup (SpecialLinearGroup (Fin p) F)} (hTw : ContainsFourierTorus ζ K)
    {t : Fin p → F} (ht : ∏ k, t k = 1) :
    ∃ g ∈ K, (g : Matrix (Fin p) (Fin p) F) =
      heisFourierMat ζ * diagonal t * (heisFourierMat ζ)⁻¹ := by
  have hΦ : IsUnit (heisFourierMat ζ : Matrix (Fin p) (Fin p) F).det :=
    isUnit_iff_ne_zero.mpr (det_heisFourierMat_ne_zero hζ)
  have hdet : (heisFourierMat ζ * diagonal t * (heisFourierMat ζ)⁻¹).det = 1 := by
    rw [Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det _).mpr hΦ), Matrix.det_diagonal, ht]
  refine ⟨⟨_, hdet⟩, hTw _ ⟨t, ?_⟩, rfl⟩
  show heisFourierMat ζ * diagonal t * (heisFourierMat ζ)⁻¹ * heisFourierMat ζ =
    heisFourierMat ζ * diagonal t
  rw [mul_assoc, Matrix.nonsing_inv_mul _ hΦ, mul_one]

theorem caseA_prod_tB (hp : 2 ≤ p) {ν : F} (hν : ν ≠ 0) :
    ∏ k : Fin p, (if (k : ℕ) = 0 then ν else if (k : ℕ) = 1 then ν⁻¹ else 1) = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 2 := ⟨p - 2, by omega⟩
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp [Fin.val_succ, hν]

theorem caseA_conj_mul {ζ : F} (hζ : IsPrimitiveRoot ζ p) (D₁ D₂ : Matrix (Fin p) (Fin p) F) :
    heisFourierMat ζ * D₁ * (heisFourierMat ζ)⁻¹ * (heisFourierMat ζ * D₂ * (heisFourierMat ζ)⁻¹) =
      heisFourierMat ζ * (D₁ * D₂) * (heisFourierMat ζ)⁻¹ := by
  have hΦ : IsUnit (heisFourierMat ζ : Matrix (Fin p) (Fin p) F).det :=
    isUnit_iff_ne_zero.mpr (det_heisFourierMat_ne_zero hζ)
  calc heisFourierMat ζ * D₁ * (heisFourierMat ζ)⁻¹ *
        (heisFourierMat ζ * D₂ * (heisFourierMat ζ)⁻¹)
      = heisFourierMat ζ * D₁ * ((heisFourierMat ζ)⁻¹ * heisFourierMat ζ) * D₂ *
        (heisFourierMat ζ)⁻¹ := by simp only [mul_assoc]
    _ = heisFourierMat ζ * (D₁ * D₂) * (heisFourierMat ζ)⁻¹ := by
      rw [Matrix.nonsing_inv_mul _ hΦ, mul_one, mul_assoc (heisFourierMat ζ) D₁ D₂]

theorem caseA_birefl_mul_inv {ζ : F} (hζ : IsPrimitiveRoot ζ p) {ν : F} (hν : ν ≠ 0) :
    fourierBirefl (p := p) ζ ν * fourierBirefl (p := p) ζ ν⁻¹ = 1 := by
  have hΦ : IsUnit (heisFourierMat ζ : Matrix (Fin p) (Fin p) F).det :=
    isUnit_iff_ne_zero.mpr (det_heisFourierMat_ne_zero hζ)
  have hD : diagonal (fun i : Fin p => if (i : ℕ) = 0 then ν else if (i : ℕ) = 1 then ν⁻¹ else 1) *
      diagonal (fun i : Fin p => if (i : ℕ) = 0 then ν⁻¹ else if (i : ℕ) = 1 then ν⁻¹⁻¹ else 1) =
      (1 : Matrix (Fin p) (Fin p) F) := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    split_ifs <;> simp [hν]
  unfold fourierBirefl
  rw [caseA_conj_mul hζ, hD, mul_one, Matrix.mul_nonsing_inv _ hΦ]

theorem caseA_birefl_ne_zero (hp : 2 ≤ p) {ζ : F} (hζ : IsPrimitiveRoot ζ p) {ν : F}
    (hν0 : ν ≠ 0) (hν1 : ν ≠ 1) (hνp : ν ^ p ≠ 1) {a b : Fin p} (hab : a ≠ b) :
    fourierBirefl ζ ν a b ≠ 0 := by
  rw [fourierBirefl_apply hp hζ hν0, if_neg hab, zero_add]
  have hp0 : (p : F) ≠ 0 := heis_natCast_ne_zero hζ hp
  have hu : (ζ ^ (a : ℕ) * (ζ ^ (b : ℕ))⁻¹) ^ p = 1 := by
    rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm (a : ℕ) p, mul_comm (b : ℕ) p, pow_mul,
      pow_mul, hζ.pow_eq_one, one_pow, one_pow, inv_one, mul_one]
  have hne : ν ≠ ζ ^ (a : ℕ) * (ζ ^ (b : ℕ))⁻¹ := fun h => hνp (by rw [h]; exact hu)
  have key : (ν - 1) + (ν⁻¹ - 1) * ζ ^ (a : ℕ) * (ζ ^ (b : ℕ))⁻¹ =
      (ν - 1) * (ν - ζ ^ (a : ℕ) * (ζ ^ (b : ℕ))⁻¹) / ν := by
    field_simp
    ring
  rw [key]
  exact mul_ne_zero (inv_ne_zero hp0)
    (div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hν1) (sub_ne_zero.mpr hne)) hν0)

theorem caseA_birefl_zero_neg [NeZero p] (hp : 2 ≤ p) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {ν : F} (hν : ν ≠ 0) (j : Fin p) :
    fourierBirefl ζ ν 0 (-j) = fourierBirefl ζ ν j 0 := by
  rw [fourierBirefl_apply hp hζ hν, fourierBirefl_apply hp hζ hν, caseA_pow_neg hζ.pow_eq_one,
    inv_inv]
  simp [zero_eq_neg]

theorem caseA_exists_sigma [NeZero p] (hp : 2 ≤ p) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {ν : F} (hν0 : ν ≠ 0) (hν1 : ν ≠ 1) (hνp : ν ^ p ≠ 1) :
    ∃ σ : Fin p → F, (∀ j, σ j ≠ 0) ∧ ∏ j, σ j = 1 ∧
      ∀ j, σ j * fourierBirefl ζ ν j 0 = fourierBirefl ζ ν 0 j := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : Fin p → F, ∀ j, N j = if j = 0 then 1 else fourierBirefl ζ ν 0 j :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Fin p → F, ∀ j, D j = if j = 0 then 1 else fourierBirefl ζ ν j 0 :=
    ⟨_, fun _ => rfl⟩
  have hNne : ∀ j, N j ≠ 0 := fun j => by
    rw [hN]
    split_ifs with hj
    · exact one_ne_zero
    · exact caseA_birefl_ne_zero hp hζ hν0 hν1 hνp (Ne.symm hj)
  have hDne : ∀ j, D j ≠ 0 := fun j => by
    rw [hD]
    split_ifs with hj
    · exact one_ne_zero
    · exact caseA_birefl_ne_zero hp hζ hν0 hν1 hνp hj
  have hND : ∏ j, N j = ∏ j, D j := by
    rw [← Equiv.prod_comp (Equiv.neg (Fin p)) N]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Equiv.neg_apply, hN, hD]
    by_cases hj : j = 0
    · simp [hj]
    · rw [if_neg (neg_ne_zero.mpr hj), if_neg hj]
      exact caseA_birefl_zero_neg hp hζ hν0 j
  refine ⟨fun j => N j / D j, fun j => div_ne_zero (hNne j) (hDne j), ?_, fun j => ?_⟩
  · rw [Finset.prod_div_distrib, hND, div_self (Finset.prod_ne_zero_iff.mpr fun j _ => hDne j)]
  · show N j / D j * _ = _
    rw [hN, hD]
    by_cases hj : j = 0
    · subst hj
      simp
    · rw [if_neg hj, if_neg hj]
      exact div_mul_cancel₀ _ (caseA_birefl_ne_zero hp hζ hν0 hν1 hνp hj)

theorem caseA_coe_inv (A : SpecialLinearGroup (Fin p) F) :
    ((A⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      (A : Matrix (Fin p) (Fin p) F)⁻¹ :=
  isolate_coe_inv_eq_of_mul_eq_one A (Matrix.mul_nonsing_inv _ (by rw [A.2]; exact isUnit_one))

theorem caseA_mulVec_e0 [NeZero p] (M : Matrix (Fin p) (Fin p) F) (j : Fin p) :
    (M *ᵥ Pi.single 0 1) j = M j 0 := by
  rw [mulVec_single_one]
  rfl

theorem caseA_e0_vecMul [NeZero p] (M : Matrix (Fin p) (Fin p) F) (j : Fin p) :
    (Pi.single 0 1 ᵥ* M) j = M 0 j := by
  rw [single_one_vecMul]
  rfl

theorem caseA_exists_mem_birefl (hp : 2 ≤ p) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {ν : F} (hν : ν ≠ 0) {K : Subgroup (SpecialLinearGroup (Fin p) F)}
    (hTw : ContainsFourierTorus ζ K) :
    (∃ B ∈ K, (B : Matrix (Fin p) (Fin p) F) = fourierBirefl ζ ν) ∧
      ∃ B ∈ K, (B : Matrix (Fin p) (Fin p) F) = (fourierBirefl ζ ν)ᵀ := by
  refine ⟨caseA_exists_mem_fourier hζ hTw (caseA_prod_tB hp hν), ?_⟩
  have hprod : ∏ k : Fin p, (if ((-k : Fin p) : ℕ) = 0 then ν else
      if ((-k : Fin p) : ℕ) = 1 then ν⁻¹ else 1) = 1 :=
    (Equiv.prod_comp (Equiv.neg (Fin p))
      (fun k : Fin p => if (k : ℕ) = 0 then ν else if (k : ℕ) = 1 then ν⁻¹ else 1)).trans
      (caseA_prod_tB hp hν)
  obtain ⟨B, hB, hBm⟩ := caseA_exists_mem_fourier hζ hTw hprod
  refine ⟨B, hB, ?_⟩
  rw [hBm]
  exact (caseA_transpose_conj hp hζ
    (fun i : Fin p => if (i : ℕ) = 0 then ν else if (i : ℕ) = 1 then ν⁻¹ else 1)).symm

theorem caseA_birefl_entries [NeZero p] (hp : 2 ≤ p) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {ν : F} (hν : ν ≠ 0) :
    (fourierBirefl ζ ν : Matrix (Fin p) (Fin p) F) 0 1 =
        (p : F)⁻¹ * ((ν - 1) + (ν⁻¹ - 1) * ζ⁻¹) ∧
      (fourierBirefl ζ ν : Matrix (Fin p) (Fin p) F) 1 0 =
        (p : F)⁻¹ * ((ν - 1) + (ν⁻¹ - 1) * ζ) := by
  have hv1 : ((1 : Fin p) : ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (show 1 < p by omega)]
  have h10 : (1 : Fin p) ≠ 0 := by
    intro h
    have h' := congrArg Fin.val h
    rw [hv1, Fin.val_zero] at h'
    exact one_ne_zero h'
  constructor
  · rw [fourierBirefl_apply hp hζ hν, if_neg h10.symm, hv1, Fin.val_zero]
    simp
  · rw [fourierBirefl_apply hp hζ hν, if_neg h10, hv1, Fin.val_zero]
    simp

theorem caseA_claim2 [NeZero p] (hp : 5 ≤ p) {ζ : F} (hζ : IsPrimitiveRoot ζ p) {ν : F}
    (hν0 : ν ≠ 0) (hν2 : ν ^ 2 ≠ 1) :
    fourierBirefl (p := p) ζ ν⁻¹ 0 1 * fourierBirefl (p := p) ζ ν 1 0 ≠
      fourierBirefl (p := p) ζ ν⁻¹ 1 0 * fourierBirefl (p := p) ζ ν 0 1 := by
  obtain ⟨h01, h10⟩ := caseA_birefl_entries (by omega) hζ hν0
  obtain ⟨i01, i10⟩ := caseA_birefl_entries (by omega) hζ (inv_ne_zero hν0)
  rw [inv_inv] at i01 i10
  rw [h01, h10, i01, i10]
  have hq0 : (p : F)⁻¹ ≠ 0 := inv_ne_zero (heis_natCast_ne_zero hζ (by omega))
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hν1 : ν - 1 ≠ 0 := sub_ne_zero.mpr fun h => hν2 (by rw [h, one_pow])
  have hν2' : 1 - ν ^ 2 ≠ 0 := sub_ne_zero.mpr fun h => hν2 h.symm
  have hab : (ν⁻¹ - 1) ^ 2 - (ν - 1) ^ 2 ≠ 0 := by
    have : (ν⁻¹ - 1) ^ 2 - (ν - 1) ^ 2 = (ν - 1) ^ 2 * (1 - ν ^ 2) / ν ^ 2 := by
      field_simp
      ring
    rw [this]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 hν1) hν2') (pow_ne_zero 2 hν0)
  have hζz : ζ - ζ⁻¹ ≠ 0 := by
    have : ζ - ζ⁻¹ = (ζ ^ 2 - 1) / ζ := by
      field_simp
    rw [this]
    exact div_ne_zero (sub_ne_zero.mpr (hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by omega))) hζ0
  intro h
  have h0 : (p : F)⁻¹ ^ 2 * (((ν⁻¹ - 1) ^ 2 - (ν - 1) ^ 2) * (ζ - ζ⁻¹)) = 0 := by
    linear_combination h
  exact mul_ne_zero (pow_ne_zero 2 hq0) (mul_ne_zero hab hζz) h0

theorem exists_fix_mem_caseA (hp : 5 ≤ p) [NeZero p] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {ν : F} (hν0 : ν ≠ 0) (hνp : ν ^ p ≠ 1) (hν2 : ν ^ 2 ≠ 1)
    {K : Subgroup (SpecialLinearGroup (Fin p) F)}
    (hT : ContainsDiagTorus K) (hTw : ContainsFourierTorus ζ K) :
    ∃ g ∈ K, (g : Matrix (Fin p) (Fin p) F) *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧
      Pi.single 0 1 ᵥ* ((g⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) ≠
        Pi.single 0 1 := by
  have hp2 : 2 ≤ p := by omega
  have hν1 : ν ≠ 1 := fun h => hν2 (by rw [h, one_pow])
  obtain ⟨⟨B, hBK, hBm⟩, ⟨Bt, hBtK, hBtm⟩⟩ := caseA_exists_mem_birefl hp2 hζ hν0 hTw
  obtain ⟨σ, hσ0, hσdet, hσ⟩ := caseA_exists_sigma hp2 hζ hν0 hν1 hνp
  have hBBi : (fourierBirefl ζ ν : Matrix (Fin p) (Fin p) F) * fourierBirefl ζ ν⁻¹ = 1 :=
    caseA_birefl_mul_inv hζ hν0
  have hBiB : (fourierBirefl ζ ν⁻¹ : Matrix (Fin p) (Fin p) F) * fourierBirefl ζ ν = 1 := by
    simpa using caseA_birefl_mul_inv hζ (inv_ne_zero hν0)
  let s : SpecialLinearGroup (Fin p) F := ⟨diagonal σ, by rw [det_diagonal, hσdet]⟩
  have hsK : s ∈ K := hT s ⟨σ, rfl⟩
  have hBinv : ((B⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      fourierBirefl ζ ν⁻¹ :=
    isolate_coe_inv_eq_of_mul_eq_one B (by rw [hBm]; exact hBBi)
  have hBtinv : ((Bt⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      (fourierBirefl ζ ν⁻¹)ᵀ :=
    isolate_coe_inv_eq_of_mul_eq_one Bt (by rw [hBtm, ← transpose_mul, hBiB, transpose_one])
  have hsinv : ((s⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      diagonal σ⁻¹ :=
    isolate_coe_inv_eq_of_mul_eq_one s (diagonal_mul_diagonal_inv_eq_one hσ0)
  refine ⟨Bt⁻¹ * s * B, K.mul_mem (K.mul_mem (K.inv_mem hBtK) hsK) hBK, ?_, ?_⟩
  ·
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hBtinv, hBm,
      ← mulVec_mulVec, ← mulVec_mulVec]
    have h1 : diagonal σ *ᵥ ((fourierBirefl ζ ν : Matrix (Fin p) (Fin p) F) *ᵥ Pi.single 0 1) =
        (fourierBirefl ζ ν : Matrix (Fin p) (Fin p) F)ᵀ *ᵥ Pi.single 0 1 := by
      funext j
      rw [mulVec_diagonal, caseA_mulVec_e0, caseA_mulVec_e0, transpose_apply]
      exact hσ j
    show (fourierBirefl ζ ν⁻¹ : Matrix (Fin p) (Fin p) F)ᵀ *ᵥ (diagonal σ *ᵥ _) = _
    rw [h1, mulVec_mulVec, ← transpose_mul, hBBi, transpose_one, one_mulVec]
  ·
    intro h
    have hginv : (Bt⁻¹ * s * B)⁻¹ = B⁻¹ * s⁻¹ * Bt := by
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, mul_assoc]
    rw [hginv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hBinv, hsinv,
      hBtm] at h
    have h2 : Pi.single 0 1 ᵥ* ((fourierBirefl ζ ν⁻¹ : Matrix (Fin p) (Fin p) F) *
        diagonal σ⁻¹) = Pi.single 0 1 ᵥ* (fourierBirefl ζ ν⁻¹ : Matrix (Fin p) (Fin p) F)ᵀ := by
      have h' := congrArg (fun v => v ᵥ* (fourierBirefl ζ ν⁻¹ : Matrix (Fin p) (Fin p) F)ᵀ) h
      simp only [vecMul_vecMul] at h'
      rwa [mul_assoc _ (fourierBirefl ζ ν : Matrix (Fin p) (Fin p) F)ᵀ, ← transpose_mul, hBiB,
        transpose_one, mul_one] at h'
    have h3 := congrFun h2 1
    rw [caseA_e0_vecMul, caseA_e0_vecMul, transpose_apply, mul_diagonal] at h3
    have h4 := hσ 1
    refine caseA_claim2 hp hζ hν0 hν2 ?_
    have h5 : (fourierBirefl ζ ν⁻¹ : Matrix (Fin p) (Fin p) F) 0 1 =
        (fourierBirefl ζ ν⁻¹ : Matrix (Fin p) (Fin p) F) 1 0 * σ 1 := by
      rw [← h3]
      simp [hσ0 1]
    rw [h5, ← h4]
    ring

theorem caseA_det_zFix [NeZero p] {ν : F} (hν : ν ≠ 0) :
    (zFix ν : Matrix (Fin p) (Fin p) F).det = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := NeZero.pos p; omega⟩
  rw [zFix, det_diagonal, Fin.prod_univ_succ]
  simp [Fin.val_succ, hν]

theorem exists_single_mem_caseA (hp : 5 ≤ p) [NeZero p] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {ν : F} (hν0 : ν ≠ 0) (hνp : ν ^ p ≠ 1) (hν2 : ν ^ 2 ≠ 1)
    {K : Subgroup (SpecialLinearGroup (Fin p) F)}
    (hT : ContainsDiagTorus K) (hTw : ContainsFourierTorus ζ K) :
    ∃ b : Fin p, b ≠ 0 ∧ ∃ c : F, c ≠ 0 ∧
      ∃ g ∈ K, (g : Matrix (Fin p) (Fin p) F) = 1 + Matrix.single 0 b c := by
  obtain ⟨g, hgK, hg0, hg1⟩ := exists_fix_mem_caseA hp hζ hν0 hνp hν2 hT hTw
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  have hxdet : IsUnit (g : Matrix (Fin p) (Fin p) F).det := by
    rw [g.2]
    exact isUnit_one
  rw [caseA_coe_inv] at hg1
  have hginve : (g : Matrix (Fin p) (Fin p) F)⁻¹ *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    calc (g : Matrix (Fin p) (Fin p) F)⁻¹ *ᵥ Pi.single 0 1
        = (g : Matrix (Fin p) (Fin p) F)⁻¹ *ᵥ
            ((g : Matrix (Fin p) (Fin p) F) *ᵥ Pi.single 0 1) := by rw [hg0]
      _ = Pi.single 0 1 := by rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ hxdet, one_mulVec]
  let z : SpecialLinearGroup (Fin p) F := ⟨zFix ν, caseA_det_zFix hν0⟩
  have hzK : z ∈ K := hT z ⟨_, rfl⟩
  have hcK : z * g * z⁻¹ * g⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem (K.mul_mem hzK hgK) (K.inv_mem hzK)) (K.inv_mem hgK)
  obtain ⟨w, hw⟩ : ∃ w : Fin p → F, w = Pi.single 0 1 ᵥ* (g : Matrix (Fin p) (Fin p) F)⁻¹ -
      Pi.single 0 1 := ⟨_, rfl⟩
  have hcm : ((z * g * z⁻¹ * g⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      1 + (1 - (ν ^ p)⁻¹) • vecMulVec (Pi.single 0 1) w := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, caseA_coe_inv z, caseA_coe_inv g, hw]
    exact zFix_comm_of_fix hxdet hg0 hν0
  have hw0 : w 0 = 0 := by
    rw [hw, Pi.sub_apply, caseA_e0_vecMul]
    have h := congrFun hginve 0
    rw [caseA_mulVec_e0] at h
    rw [h]
    simp
  have hwne : ∃ b, w b ≠ 0 := by
    by_contra hcon
    apply hg1
    funext b
    have h0 : w b = 0 := by
      by_contra h
      exact hcon ⟨b, h⟩
    rw [hw, Pi.sub_apply, sub_eq_zero] at h0
    exact h0
  obtain ⟨b, hb⟩ := hwne
  have hb0 : b ≠ 0 := fun h => hb (h ▸ hw0)
  have hρ : (1 : F) - (ν ^ p)⁻¹ ≠ 0 := sub_ne_zero.mpr fun h => hνp (inv_eq_one.mp h.symm)
  have hMsupp : RootSuppIn {0} ((1 - (ν ^ p)⁻¹) • vecMulVec (Pi.single 0 1) w) := by
    intro a b' hab'
    rw [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul] at hab'
    have ha : a = 0 := by
      by_contra ha
      apply hab'
      rw [Pi.single_eq_of_ne ha, zero_mul, mul_zero]
    refine ⟨Finset.mem_singleton.mpr ha, fun hb' => hab' ?_⟩
    rw [Finset.mem_singleton.mp hb', hw0, mul_zero, mul_zero]
  have hMab : ((1 - (ν ^ p)⁻¹) • vecMulVec (Pi.single 0 1) w :
      Matrix (Fin p) (Fin p) F) 0 b ≠ 0 := by
    rw [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, Pi.single_eq_same, one_mul]
    exact mul_ne_zero hρ hb
  obtain ⟨c, hc, g', hg'K, hg'⟩ := exists_single_mem_of_suppIn hp hζ0 hζ1 hT hMsupp hMab
    ⟨_, hcK, hcm⟩
  exact ⟨b, hb0, c, hc, g', hg'K, hg'⟩

end CFSG.LieType.SeitzGeneration

end
