module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutFrame
public import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtBd
import CFSG.GH74.Generic.BProg.B2.GenLocL5Sign
public import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtFrame
public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutNF
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.Generic.S1.Uni Matrix

namespace GenLocU4OutFrSplit

open GenLocU4ExtBd

variable {p f : ℕ} {K : Type} [Field K]

theorem gram_bar2 (h : UnitaryFieldData p f K) {g₁ P₀ : Matrix (Fin 2) (Fin 2) K}
    (hu : cT h g₁ * g₁ = 1) (hP : g₁ * P₀.map h.bar = P₀) :
    (cT h P₀ * P₀).map h.bar = cT h P₀ * P₀ ∧ (cT h P₀ * P₀)ᵀ = cT h P₀ * P₀ := by
  have e1 : cT h P₀ * P₀ = (cT h P₀).map h.bar * P₀.map h.bar := by
    have e : cT h P₀ * P₀ = cT h (g₁ * P₀.map h.bar) * (g₁ * P₀.map h.bar) := by rw [hP]
    rw [e, cT_mul]
    have e2 : cT h (P₀.map h.bar) = (cT h P₀).map h.bar := by
      simp [cT, Matrix.transpose_map]
    rw [e2, Matrix.mul_assoc, ← Matrix.mul_assoc (cT h g₁) g₁, hu, Matrix.one_mul]
  have e3 : (cT h P₀ * P₀).map h.bar = (cT h P₀).map h.bar * P₀.map h.bar := Matrix.map_mul
  have hb : (cT h P₀ * P₀).map h.bar = cT h P₀ * P₀ := by rw [e3, ← e1]
  refine ⟨hb, ?_⟩
  have hsym : cT h (cT h P₀ * P₀) = cT h P₀ * P₀ := by rw [cT_mul, cT_cT]
  rw [cT_def, hb] at hsym
  exact hsym


theorem cT_diagonal2 (h : UnitaryFieldData p f K) (d : Fin 2 → K) :
    cT h (Matrix.diagonal d) = Matrix.diagonal (fun i => h.bar (d i)) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [cT]
  · simp [cT, hij, Matrix.diagonal_apply_ne, Ne.symm hij]

theorem exists_sym2_nf [Finite K] (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {C : Matrix (Fin 2) (Fin 2) K} (hCt : Cᵀ = C) (hCU : cT h C * C = 1) :
    ∃ (V : Matrix (Fin 2) (Fin 2) K) (ε : Fin 2 → K), cT h V * V = 1 ∧
      (∀ i, ε i * h.bar (ε i) = 1) ∧ C * V.map h.bar = V * Matrix.diagonal ε := by
  classical
  have hfinK : Finite K := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have hcT : cT h C = C.map h.bar := by
    rw [cT, ← Matrix.transpose_map, hCt]
  have hCC : C * C.map h.bar = 1 := by
    rw [hcT] at hCU
    exact mul_eq_one_comm.mp hCU
  let σ : K ≃+* K := RingEquiv.ofBijective h.bar ⟨h.bar.injective, fun c => ⟨h.bar c, h.bar_bar c⟩⟩
  have hσ : ∀ c, σ c = h.bar c := fun c => rfl
  let T : (Fin 2 → K) → (Fin 2 → K) := fun v => C *ᵥ fun i => h.bar (v i)
  have hbarvec : ∀ (N : Matrix (Fin 2) (Fin 2) K) (v : Fin 2 → K), (fun i => h.bar ((N *ᵥ v) i)) =
      N.map h.bar *ᵥ fun i => h.bar (v i) := fun N v => funext fun i =>
    RingHom.map_mulVec h.bar N v i
  obtain ⟨x₀, hx₀⟩ := h.exists_bar_ne
  obtain ⟨H, hH⟩ := LinearFlag.exists_fixed_basis_of_ne (σ := σ) (x₀ := x₀)
    (by rw [hσ]; exact hx₀) T
    (fun v w => by
      show C *ᵥ (fun i => h.bar (v i + w i)) =
        C *ᵥ (fun i => h.bar (v i)) + C *ᵥ (fun i => h.bar (w i))
      rw [← Matrix.mulVec_add]
      congr 1
      funext i
      simp)
    (fun c v => by
      show C *ᵥ (fun i => h.bar (c * v i)) = σ c • (C *ᵥ fun i => h.bar (v i))
      rw [hσ, ← Matrix.mulVec_smul]
      congr 1
      funext i
      simp)
    (fun v => by
      show C *ᵥ (fun i => h.bar ((C *ᵥ fun i => h.bar (v i)) i)) = v
      rw [hbarvec C (fun i => h.bar (v i))]
      have hv : (fun i => h.bar (h.bar (v i))) = v := funext fun i => h.bar_bar _
      rw [hv, Matrix.mulVec_mulVec, hCC, Matrix.one_mulVec])
  obtain ⟨P₀, hP₀def⟩ : ∃ P₀ : Matrix (Fin 2) (Fin 2) K, P₀ = (H : Matrix (Fin 2) (Fin 2) K) :=
    ⟨_, rfl⟩
  have hP₀ : C * P₀.map h.bar = P₀ := by
    rw [hP₀def]
    ext r c
    have := congrFun (hH c) r
    simp only [T, Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, Matrix.map_apply]
    exact this
  have hdet₀ : P₀.det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det H).isUnit
    rw [hP₀def]
    simpa using this.ne_zero
  obtain ⟨hbar, hsym⟩ := gram_bar2 h hCU hP₀
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Matrix (Fin 2) (Fin 2) K, S₀ = cT h P₀ * P₀ := ⟨_, rfl⟩
  rw [← hS₀] at hbar hsym
  obtain ⟨S', hS'⟩ := exists_fixedField_matrix h hbar
  have hι : Function.Injective h.fixedField.subtype := Subtype.val_injective
  have hS'sym : S'ᵀ = S' := by
    apply Matrix.map_injective hι
    show S'ᵀ.map h.fixedField.subtype = S'.map h.fixedField.subtype
    rw [Matrix.transpose_map, hS', hsym]
  have hdetcT : ∀ M : Matrix (Fin 2) (Fin 2) K, (cT h M).det = h.bar M.det := fun M => by
    rw [cT, Matrix.det_transpose]
    exact (RingHom.map_det (h.bar : K →+* K) M).symm
  have hdetS : S₀.det ≠ 0 := by
    rw [hS₀, Matrix.det_mul, hdetcT]
    exact mul_ne_zero ((map_ne_zero h.bar).2 hdet₀) hdet₀
  have hdetS' : S'.det ≠ 0 := by
    intro h0
    apply hdetS
    have := RingHom.map_det h.fixedField.subtype S'
    rw [h0, map_zero, RingHom.mapMatrix_apply, hS'] at this
    exact this.symm
  have hodd : Odd (Nat.card h.fixedField) := by
    rw [h.card_fixedField]
    exact (h.prime.odd_of_ne_two hp2).pow
  have : Finite h.fixedField := inferInstance
  obtain ⟨Q', hQ'⟩ := GenLocL5Sign.exists_orthogonal_congr
    (GenLocU4OutFrame.ringChar_ne_two_of_odd hodd) S' hS'sym
  set Q : Matrix (Fin 2) (Fin 2) K :=
    (Q' : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype with hQdef
  have hQbar : Q.map h.bar = Q := map_fixedField_bar h _
  have hcTQ : cT h Q = Qᵀ := by rw [cT, hQbar]
  have hdetQ : Q.det ≠ 0 := by
    have := RingHom.map_det h.fixedField.subtype (Q' : Matrix (Fin 2) (Fin 2) h.fixedField)
    rw [RingHom.mapMatrix_apply] at this
    rw [hQdef, ← this]
    intro h0
    have h1 : ((Q' : Matrix (Fin 2) (Fin 2) h.fixedField)).det = 0 := hι (by simpa using h0)
    exact ((Matrix.isUnit_iff_isUnit_det _).1 Q'.isUnit).ne_zero h1
  set D : Matrix (Fin 2) (Fin 2) K := Qᵀ * S₀ * Q with hD
  have hDeq : D = ((Q' : Matrix (Fin 2) (Fin 2) h.fixedField)ᵀ * S' *
      (Q' : Matrix (Fin 2) (Fin 2) h.fixedField)).map h.fixedField.subtype := by
    rw [hD, hQdef, ← hS']
    simp only [Matrix.map_mul, Matrix.transpose_map]
  have hDdiag : D = Matrix.diagonal (fun i => D i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij, hDeq]
      have := hQ' i j hij
      simp only [Matrix.map_apply, this, map_zero]
  have hDbar : D.map h.bar = D := by rw [hDeq]; exact map_fixedField_bar h _
  have hdetD : D.det ≠ 0 := by
    rw [hD, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hdetQ hdetS) hdetQ
  have hd0 : ∀ i, D i i ≠ 0 := by
    intro i h0
    apply hdetD
    rw [hDdiag, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa using h0)
  have hdfix : ∀ i, h.bar (D i i) = D i i := fun i => by
    have := congrFun (congrFun hDbar i) i
    simpa using this
  have hKcard : Nat.card K = (p ^ f) ^ 2 := by
    rw [h.card]; ring_nf
  have hlam : ∀ i, ∃ c : K, h.bar c * c = (D i i)⁻¹ := by
    intro i
    have hfix : CFSG.LieType.BorelTits.unitaryInvolution K p f (D i i)⁻¹ = (D i i)⁻¹ := by
      rw [CFSG.LieType.BorelTits.unitaryInvolution_apply]
      have := hdfix i
      rw [UnitaryFieldData.bar_apply] at this
      rw [inv_pow, this]
    obtain ⟨c, hc⟩ := CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed hKcard hfix
      (inv_ne_zero (hd0 i))
    exact ⟨c, by rw [CFSG.LieType.BorelTits.unitaryInvolution_apply] at hc; exact hc⟩
  choose lam hlam using hlam
  have hlam0 : ∀ i, lam i ≠ 0 := by
    intro i h0
    have := hlam i
    rw [h0, mul_zero] at this
    exact inv_ne_zero (hd0 i) this.symm
  have hbar0 : ∀ i, h.bar (lam i) ≠ 0 := fun i => (map_ne_zero h.bar).2 (hlam0 i)
  set Lam : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal lam with hLam
  set P₂ : Matrix (Fin 2) (Fin 2) K := P₀ * Q * Lam with hP₂
  have hunit : cT h P₂ * P₂ = 1 := by
    have e1 : cT h P₂ * P₂ = cT h Lam * (Qᵀ * (cT h P₀ * P₀) * Q) * Lam := by
      rw [hP₂, cT_mul h (P₀ * Q) Lam, cT_mul h P₀ Q, hcTQ]
      simp only [Matrix.mul_assoc]
    rw [← hS₀] at e1
    rw [e1, ← hD, hDdiag, hLam, cT_diagonal2, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      have := hlam i
      have hd := hd0 i
      calc h.bar (lam i) * D i i * lam i = (h.bar (lam i) * lam i) * D i i := by ring
        _ = 1 := by rw [this]; exact inv_mul_cancel₀ hd
    · simp [hij]
  have hBP : C * P₂.map h.bar = P₂ * Matrix.diagonal (fun i => (lam i)⁻¹ * h.bar (lam i)) := by
    have e2 : P₂.map h.bar = P₀.map h.bar * Q * Lam.map h.bar := by
      rw [hP₂, Matrix.map_mul, Matrix.map_mul, hQbar]
    rw [e2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP₀, hP₂, Matrix.mul_assoc (P₀ * Q), hLam,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_map (map_zero _)]
    congr 2
    funext i
    rw [← mul_assoc, mul_inv_cancel₀ (hlam0 i), one_mul]
  refine ⟨P₂, fun i => (lam i)⁻¹ * h.bar (lam i), hunit, fun i => ?_, hBP⟩
  rw [map_mul, map_inv₀, h.bar_bar]
  field_simp [hlam0 i, hbar0 i]


theorem exists_sym2_nf_pm [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f % 4 = 1) {C : Matrix (Fin 2) (Fin 2) K} (hCt : Cᵀ = C)
    (hCU : (C.map (· ^ (p ^ f)))ᵀ * C = 1) :
    ∃ (V : Matrix (Fin 2) (Fin 2) K) (σ : Fin 2 → K), (V.map (· ^ (p ^ f)))ᵀ * V = 1 ∧
      (∀ i, σ i = 1 ∨ σ i = -1) ∧ C * V.map (· ^ (p ^ f)) = V * Matrix.diagonal σ := by
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  have hcT : ∀ M : Matrix (Fin 2) (Fin 2) K, cT h M = (M.map (· ^ (p ^ f)))ᵀ := fun M => by
    rw [cT, GenLocU4ExtFrame.map_bar_eq h]
  obtain ⟨V₀, ε, hV₀, hε, hCV⟩ := exists_sym2_nf h hp2 hCt (by rw [hcT]; exact hCU)
  have hε' : ∀ i, ε i ^ (p ^ f + 1) = 1 := fun i => by
    have := hε i
    rw [UnitaryFieldData.bar_apply] at this
    rwa [pow_succ']
  choose ω σ hω hσ hεω using fun i => GenLocU4OutFrame.exists_pm_omega hp hp2 hK hq (hε' i)
  have hωb : ∀ i, h.bar (ω i) * ω i = 1 := fun i => by
    rw [UnitaryFieldData.bar_apply, ← pow_succ, hω i]
  refine ⟨V₀ * Matrix.diagonal ω, σ, ?_, hσ, ?_⟩
  · rw [← hcT, cT_mul, cT_diagonal2]
    calc Matrix.diagonal (fun i => h.bar (ω i)) * cT h V₀ * (V₀ * Matrix.diagonal ω)
        = Matrix.diagonal (fun i => h.bar (ω i)) * (cT h V₀ * V₀) * Matrix.diagonal ω := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hV₀, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
          ext i j
          by_cases hij : i = j
          · subst hij; simp [hωb]
          · simp [hij]
  · have hmap : (V₀ * Matrix.diagonal ω).map (· ^ (p ^ f)) =
        V₀.map h.bar * Matrix.diagonal (fun i => h.bar (ω i)) := by
      rw [← GenLocU4ExtFrame.map_bar_eq h, Matrix.map_mul, Matrix.diagonal_map (map_zero _)]
    rw [hmap, ← Matrix.mul_assoc, hCV, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 3
    funext i
    calc ε i * h.bar (ω i) = (ω i * ω i * σ i) * h.bar (ω i) := by rw [← hεω i]
      _ = ω i * σ i * (h.bar (ω i) * ω i) := by ring
      _ = ω i * σ i := by rw [hωb i, mul_one]

theorem bd_transpose (B B' : Matrix (Fin 2) (Fin 2) K) : (bd B B')ᵀ = bd Bᵀ B'ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd]

theorem bd_map {q : ℕ} (hq : q ≠ 0) (B B' : Matrix (Fin 2) (Fin 2) K) :
    (bd B B').map (· ^ q) = bd (B.map (· ^ q)) (B'.map (· ^ q)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd, zero_pow hq]

theorem bd_diag (a b : Fin 2 → K) :
    bd (Matrix.diagonal a) (Matrix.diagonal b) = Matrix.diagonal ![a 0, a 1, b 0, b 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd, Matrix.diagonal]

theorem twist_symm (h : UnitaryFieldData p f K) (U B : Matrix (Fin 4) (Fin 4) K) (hB : Bᵀ = B) :
    (cT h U * B * U.map h.bar)ᵀ = cT h U * B * U.map h.bar := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hB]
  have e1 : (U.map h.bar)ᵀ = cT h U := rfl
  have e2 : (cT h U)ᵀ = U.map h.bar := Matrix.transpose_transpose _
  rw [e1, e2, Matrix.mul_assoc]

theorem twist_unitary (h : UnitaryFieldData p f K) (U B : Matrix (Fin 4) (Fin 4) K)
    (hU : cT h U * U = 1) (hB : cT h B * B = 1) :
    cT h (cT h U * B * U.map h.bar) * (cT h U * B * U.map h.bar) = 1 := by
  have hUU : U * cT h U = 1 := mul_eq_one_comm.mp hU
  have e3 : cT h (U.map h.bar) = Uᵀ := by
    ext i j
    simp [cT, h.bar_bar]
  have e4 : Uᵀ * U.map h.bar = 1 := by
    have := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M.map h.bar) hU
    simp only [Matrix.map_mul, cT, Matrix.transpose_map, map_bar_bar h] at this
    rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this
  rw [cT_mul, cT_mul, cT_cT, e3]
  calc Uᵀ * (cT h B * U) * (cT h U * B * U.map h.bar)
      = Uᵀ * cT h B * (U * cT h U) * B * U.map h.bar := by simp only [Matrix.mul_assoc]
    _ = Uᵀ * (cT h B * B) * U.map h.bar := by rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hB, Matrix.mul_one, e4]


theorem twist_comm (h : UnitaryFieldData p f K) {x U B D : Matrix (Fin 4) (Fin 4) K}
    (hxB : x * B = B * x.map h.bar) (hxU : x * U = U * D) (hDbar : D.map h.bar = D)
    (hDc : cT h D = D) (hcx : cT h x = x) :
    (cT h U * B * U.map h.bar) * D = D * (cT h U * B * U.map h.bar) := by
  have e1 : U.map h.bar * D = x.map h.bar * U.map h.bar := by
    have := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M.map h.bar) hxU
    simp only [Matrix.map_mul, hDbar] at this
    exact this.symm
  have e2 : cT h U * x = D * cT h U := by
    have := congrArg (cT h) hxU
    rw [cT_mul, cT_mul, hcx, hDc] at this
    exact this
  calc cT h U * B * U.map h.bar * D = cT h U * B * (U.map h.bar * D) := by rw [Matrix.mul_assoc]
    _ = cT h U * (B * x.map h.bar) * U.map h.bar := by rw [e1]; simp only [Matrix.mul_assoc]
    _ = cT h U * (x * B) * U.map h.bar := by rw [hxB]
    _ = (cT h U * x) * B * U.map h.bar := by simp only [Matrix.mul_assoc]
    _ = D * (cT h U * B * U.map h.bar) := by rw [e2]; simp only [Matrix.mul_assoc]

theorem exists_frame_pair [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f % 4 = 1) {x B : Matrix (Fin 4) (Fin 4) K}
    (hx : (x.map (· ^ (p ^ f)))ᵀ * x = 1) (hx2 : x * x = 1) (htr : x.trace = 0)
    (hB : (B.map (· ^ (p ^ f)))ᵀ * B = 1) (hBt : Bᵀ = B)
    (hxB : x * B = B * x.map (· ^ (p ^ f))) :
    ∃ (U : Matrix (Fin 4) (Fin 4) K) (σ : Fin 4 → K), (U.map (· ^ (p ^ f)))ᵀ * U = 1 ∧
      x * U = U * Matrix.diagonal ![-1, -1, 1, 1] ∧ (∀ i, σ i = 1 ∨ σ i = -1) ∧
      B * U.map (· ^ (p ^ f)) = U * Matrix.diagonal σ := by
  classical
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  have h2 : (2 : K) ≠ 0 := GenLocU4ExtFrame.two_ne_zero_of_card hp hp2 hK
  have hq0 : p ^ f ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hbarq : ∀ M : Matrix (Fin 4) (Fin 4) K, M.map h.bar = M.map (· ^ (p ^ f)) := fun M =>
    GenLocU4ExtFrame.map_bar_eq h M
  have hcT : ∀ M : Matrix (Fin 4) (Fin 4) K, cT h M = (M.map (· ^ (p ^ f)))ᵀ := fun M => by
    rw [cT, hbarq]
  let xg : GL (Fin 4) K := ⟨x, x, hx2, hx2⟩
  obtain ⟨P, hPU, hxP⟩ := GenLocU4ExtFrame.exists_frame hp hp2 hK xg hx (Units.ext hx2) htr
  set U1 : Matrix (Fin 4) (Fin 4) K := (P : Matrix (Fin 4) (Fin 4) K) with hU1
  set D : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![-1, -1, 1, 1] with hD
  have hxU1 : x * U1 = U1 * D := hxP
  have hU1c : cT h U1 * U1 = 1 := by rw [hcT]; exact hPU
  have hxc : cT h x = x := by
    have hxc1 : cT h x * x = 1 := by rw [hcT]; exact hx
    calc cT h x = cT h x * (x * x) := by rw [hx2, Matrix.mul_one]
      _ = (cT h x * x) * x := by rw [Matrix.mul_assoc]
      _ = x := by rw [hxc1, Matrix.one_mul]
  have hDbar : D.map h.bar = D := by
    rw [hD, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    fin_cases i <;> simp
  have hDc : cT h D = D := by
    rw [cT, hDbar, hD, Matrix.diagonal_transpose]
  have hBc : cT h B * B = 1 := by rw [hcT]; exact hB
  have hxB' : x * B = B * x.map h.bar := by rw [hbarq]; exact hxB
  set B1 : Matrix (Fin 4) (Fin 4) K := cT h U1 * B * U1.map h.bar with hB1
  have hB1t : B1ᵀ = B1 := twist_symm h U1 B hBt
  have hB1u : cT h B1 * B1 = 1 := twist_unitary h U1 B hU1c hBc
  have hB1D : B1 * D = D * B1 := twist_comm h hxB' hxU1 hDbar hDc hxc
  have hBU1 : B * U1.map h.bar = U1 * B1 := by
    have hUU : U1 * cT h U1 = 1 := mul_eq_one_comm.mp hU1c
    rw [hB1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  obtain ⟨Bp, Bm, hbd⟩ := exists_bd_of_comm h2 B1 hB1D
  have hBpt : Bpᵀ = Bp ∧ Bmᵀ = Bm := by
    have := hB1t
    rw [hbd, bd_transpose] at this
    exact bd_inj this
  have hBpu : (Bp.map (· ^ (p ^ f)))ᵀ * Bp = 1 ∧ (Bm.map (· ^ (p ^ f)))ᵀ * Bm = 1 := by
    have := hB1u
    rw [hcT, hbd, bd_unitary hq0, ← bd_one] at this
    exact bd_inj this
  obtain ⟨Vp, σp, hVpu, hσp, hBpV⟩ := exists_sym2_nf_pm hp hp2 hK hq hBpt.1 hBpu.1
  obtain ⟨Vm, σm, hVmu, hσm, hBmV⟩ := exists_sym2_nf_pm hp hp2 hK hq hBpt.2 hBpu.2
  set U2 : Matrix (Fin 4) (Fin 4) K := bd Vp Vm with hU2
  set σ : Fin 4 → K := ![σp 0, σp 1, σm 0, σm 1] with hσdef
  have hU2u : (U2.map (· ^ (p ^ f)))ᵀ * U2 = 1 := by
    rw [hU2, bd_unitary hq0, hVpu, hVmu, bd_one]
  have hσD : Matrix.diagonal σ = bd (Matrix.diagonal σp) (Matrix.diagonal σm) :=
    (bd_diag σp σm).symm
  have hB1U2 : B1 * U2.map h.bar = U2 * Matrix.diagonal σ := by
    rw [hbarq, hU2, bd_map hq0, hbd, bd_mul, hBpV, hBmV, hσD, bd_mul]
  refine ⟨U1 * U2, σ, ?_, ?_, ?_, ?_⟩
  · rw [← hcT, cT_mul]
    calc cT h U2 * cT h U1 * (U1 * U2) = cT h U2 * (cT h U1 * U1) * U2 := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU1c, Matrix.mul_one, hcT]; exact hU2u
  · have hDU2 : D * U2 = U2 * D := by
      rw [hD, diag_eq_bd, hU2, bd_mul, bd_mul]
      simp
    calc x * (U1 * U2) = (x * U1) * U2 := by rw [Matrix.mul_assoc]
      _ = U1 * (D * U2) := by rw [hxU1]; simp only [Matrix.mul_assoc]
      _ = U1 * (U2 * D) := by rw [hDU2]
      _ = U1 * U2 * D := by rw [Matrix.mul_assoc]
  · intro i
    fin_cases i
    · exact hσp 0
    · exact hσp 1
    · exact hσm 0
    · exact hσm 1
  · calc B * (U1 * U2).map (· ^ (p ^ f)) = B * (U1.map h.bar * U2.map h.bar) := by
          rw [← hbarq, Matrix.map_mul]
      _ = (B * U1.map h.bar) * U2.map h.bar := by rw [Matrix.mul_assoc]
      _ = U1 * (B1 * U2.map h.bar) := by rw [hBU1, Matrix.mul_assoc]
      _ = U1 * (U2 * Matrix.diagonal σ) := by rw [hB1U2]
      _ = U1 * U2 * Matrix.diagonal σ := by rw [Matrix.mul_assoc]


theorem det_cT (h : UnitaryFieldData p f K) (M : Matrix (Fin 4) (Fin 4) K) :
    (cT h M).det = h.bar M.det := by
  rw [cT, Matrix.det_transpose]
  exact (RingHom.map_det (h.bar : K →+* K) M).symm

theorem prod_ne_one (h : UnitaryFieldData p f K) {B U : Matrix (Fin 4) (Fin 4) K} {σ : Fin 4 → K}
    (hU : cT h U * U = 1) (hBU : B * U.map h.bar = U * Matrix.diagonal σ)
    (hmin : ∀ μ : K, μ ^ (p ^ f + 1) = 1 → μ * μ ≠ B.det) : σ 0 * σ 1 * σ 2 * σ 3 ≠ 1 := by
  intro hs
  have hdet := congrArg Matrix.det hBU
  have hmapdet : (U.map h.bar).det = h.bar U.det := (RingHom.map_det (h.bar : K →+* K) U).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_four, hs, hmapdet] at hdet
  have hn : h.bar U.det * U.det = 1 := by
    have := congrArg Matrix.det hU
    rw [Matrix.det_mul, det_cT, Matrix.det_one] at this
    exact this
  have hnorm : U.det ^ (p ^ f + 1) = 1 := by
    rw [pow_succ, ← UnitaryFieldData.bar_apply h]
    exact hn
  exact hmin U.det hnorm (by linear_combination (B.det) * hn - U.det * hdet)

theorem exists_perm (σ : Fin 4 → K) (hσ : ∀ i, σ i = 1 ∨ σ i = -1)
    (hs : σ 0 * σ 1 * σ 2 * σ 3 ≠ 1) :
    ∃ π : Fin 4 → Fin 4, Function.Injective π ∧
      ((∀ k, (![-1, -1, 1, 1] : Fin 4 → K) (π k) = (![1, 1, -1, -1] : Fin 4 → K) k) ∨
        (∀ k, (![-1, -1, 1, 1] : Fin 4 → K) (π k) = (![-1, -1, 1, 1] : Fin 4 → K) k)) ∧
      ((∀ k, σ (π k) = (![1, 1, 1, -1] : Fin 4 → K) k) ∨
        (∀ k, σ (π k) = (![-1, -1, -1, 1] : Fin 4 → K) k)) := by
  rcases hσ 0 with h0 | h0 <;> rcases hσ 1 with h1 | h1 <;> rcases hσ 2 with h2 | h2 <;>
    rcases hσ 3 with h3 | h3 <;> rw [h0, h1, h2, h3] at hs
  · exact absurd (by norm_num) hs
  · exact ⟨![0, 1, 2, 3], by decide, Or.inr fun k => by fin_cases k <;> simp,
      Or.inl fun k => by fin_cases k <;> simp [h0, h1, h2, h3]⟩
  · exact ⟨![0, 1, 3, 2], by decide, Or.inr fun k => by fin_cases k <;> simp,
      Or.inl fun k => by fin_cases k <;> simp [h0, h1, h2, h3]⟩
  · exact absurd (by norm_num) hs
  · exact ⟨![2, 3, 0, 1], by decide, Or.inl fun k => by fin_cases k <;> simp,
      Or.inl fun k => by fin_cases k <;> simp [h0, h1, h2, h3]⟩
  · exact absurd (by norm_num) hs
  · exact absurd (by norm_num) hs
  · exact ⟨![2, 3, 1, 0], by decide, Or.inl fun k => by fin_cases k <;> simp,
      Or.inr fun k => by fin_cases k <;> simp [h0, h1, h2, h3]⟩
  · exact ⟨![2, 3, 1, 0], by decide, Or.inl fun k => by fin_cases k <;> simp,
      Or.inl fun k => by fin_cases k <;> simp [h0, h1, h2, h3]⟩
  · exact absurd (by norm_num) hs
  · exact absurd (by norm_num) hs
  · exact ⟨![2, 3, 0, 1], by decide, Or.inl fun k => by fin_cases k <;> simp,
      Or.inr fun k => by fin_cases k <;> simp [h0, h1, h2, h3]⟩
  · exact absurd (by norm_num) hs
  · exact ⟨![0, 1, 3, 2], by decide, Or.inr fun k => by fin_cases k <;> simp,
      Or.inr fun k => by fin_cases k <;> simp [h0, h1, h2, h3]⟩
  · exact ⟨![0, 1, 2, 3], by decide, Or.inr fun k => by fin_cases k <;> simp,
      Or.inr fun k => by fin_cases k <;> simp [h0, h1, h2, h3]⟩
  · exact absurd (by norm_num) hs

theorem mul_diag_submatrix {X W U : Matrix (Fin 4) (Fin 4) K} (ε : Fin 4 → K) (π : Fin 4 → Fin 4)
    (h : X * W = U * Matrix.diagonal ε) :
    X * W.submatrix id π = U.submatrix id π * Matrix.diagonal (fun k => ε (π k)) := by
  ext r k
  have e1 := congrFun (congrFun h r) (π k)
  rw [Matrix.mul_diagonal] at e1
  rw [Matrix.mul_diagonal]
  simpa [Matrix.mul_apply, Matrix.submatrix_apply] using e1


open GenLocU4Basic GenLocU4Out in
theorem exists_split_frame {p f : ℕ} {K : Type} [Field K] [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    {x B : Matrix (Fin 4) (Fin 4) K} (hx : IsUnitaryU (p ^ f) x) (hx2 : x * x = 1) (htr : x.trace = 0)
    (hB : IsUnitaryU (p ^ f) B) (hmin : IsMinusU (p ^ f) B)
    (hxB : x * B = B * x.map (· ^ (p ^ f))) :
    ∃ U : Matrix (Fin 4) (Fin 4) K, IsUnitaryU (p ^ f) U ∧
      (x * U = U * (tT : Matrix (Fin 4) (Fin 4) K) ∨ x * U = U * (-(tT : Matrix (Fin 4) (Fin 4) K))) ∧
      (B * U.map (· ^ (p ^ f)) = U * (mD : Matrix (Fin 4) (Fin 4) K) ∨
        B * U.map (· ^ (p ^ f)) = U * (-(mD : Matrix (Fin 4) (Fin 4) K))) := by
  classical
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  obtain ⟨U, σ, hU, hxU, hσ, hBU⟩ := exists_frame_pair hp hp2 hK hq hx hx2 htr hB hmin.1 hxB
  have hne : σ 0 * σ 1 * σ 2 * σ 3 ≠ 1 :=
    prod_ne_one h ((GenLocU4OutFrame.isUnitaryU_iff_cT h U).1 hU)
      (by rw [GenLocU4ExtFrame.map_bar_eq h]; exact hBU) hmin.2
  obtain ⟨π, hπinj, hπD, hπσ⟩ := exists_perm σ hσ hne
  have e1 := mul_diag_submatrix (![-1, -1, 1, 1] : Fin 4 → K) π hxU
  have e2 : B * (U.submatrix id π).map (· ^ (p ^ f)) =
      U.submatrix id π * Matrix.diagonal (fun k => σ (π k)) := mul_diag_submatrix σ π hBU
  have hnegT : -(tT : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![-1, -1, 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [tT, Matrix.diagonal]
  have hnegD : -(mD : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![-1, -1, -1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mD, Matrix.diagonal]
  refine ⟨U.submatrix id π, GenLocU4ExtFrame.submatrix_unitary U hU π hπinj, ?_, ?_⟩
  · rcases hπD with hD | hD
    · left
      rw [e1, show (fun k => (![-1, -1, 1, 1] : Fin 4 → K) (π k)) = ![1, 1, -1, -1] from funext hD]
      rfl
    · right
      rw [e1, show (fun k => (![-1, -1, 1, 1] : Fin 4 → K) (π k)) = ![-1, -1, 1, 1] from funext hD,
        hnegT]
  · rcases hπσ with hS | hS
    · left
      rw [e2, show (fun k => σ (π k)) = ![1, 1, 1, -1] from funext hS]
      rfl
    · right
      rw [e2, show (fun k => σ (π k)) = ![-1, -1, -1, 1] from funext hS, hnegD]

end GenLocU4OutFrSplit

end CFSG.GH74.Generic.BProg.B2
