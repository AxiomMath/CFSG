module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4Dich
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutE16
public import CFSG.GH74.Generic.S1.UniAdapted
import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtMu
import CFSG.GH74.Generic.BProg.B2.GenLocL5Sign

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.Generic.S1.Uni Matrix

namespace GenLocU4OutFrame

variable {p f : ℕ} {K : Type} [Field K]

theorem ringChar_ne_two_of_odd {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) : ringChar F ≠ 2 := by
  intro h
  have : CharP F 2 := by rw [← h]; exact ringChar.charP F
  have := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F 2
  have h2 : Nat.card F = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hn1 : 1 ≤ (n : ℕ) := n.pos
  have h3 : 2 ∣ Nat.card F := by rw [h2]; exact dvd_pow_self 2 (by omega)
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h3)

theorem cT_diagonal (h : UnitaryFieldData p f K) (d : Fin 4 → K) :
    cT h (Matrix.diagonal d) = Matrix.diagonal (fun i => h.bar (d i)) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [cT]
  · simp [cT, hij, Matrix.diagonal_apply_ne, Ne.symm hij]

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher in
theorem exists_sym_nf [Finite K] (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) {B : Matrix (Fin 4) (Fin 4) K}
    (hBt : Bᵀ = B) (hBU : cT h B * B = 1) :
    ∃ (U : Matrix (Fin 4) (Fin 4) K) (ε : Fin 4 → K), cT h U * U = 1 ∧ (∀ i, ε i * h.bar (ε i) = 1) ∧
      B = U * Matrix.diagonal ε * Uᵀ := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have hfinK : Finite K := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have hcT : cT h B = B.map h.bar := by
    rw [cT, ← Matrix.transpose_map, hBt]
  have hBB : B * B.map h.bar = 1 := by
    rw [hcT] at hBU
    exact mul_eq_one_comm.mp hBU
  obtain ⟨P₀, hdet₀, hP₀⟩ := exists_fixed_basis h h2 hBB
  have hu1 : cT h B * B = (1 : K) • (1 : Matrix (Fin 4) (Fin 4) K) := by rw [one_smul]; exact hBU
  obtain ⟨hbar, hsym⟩ := gram_bar h (Or.inl rfl) hu1 hP₀
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Matrix (Fin 4) (Fin 4) K, S₀ = cT h P₀ * P₀ := ⟨_, rfl⟩
  rw [← hS₀] at hbar hsym
  have hbar' : S₀.map h.bar = S₀ := by rw [hbar, one_smul]
  have hsym' : S₀ᵀ = S₀ := by rw [hsym, one_smul]
  obtain ⟨S', hS'⟩ := exists_fixedField_matrix h hbar'
  have hι : Function.Injective h.fixedField.subtype := Subtype.val_injective
  have hS'sym : S'ᵀ = S' := by
    apply Matrix.map_injective hι
    show S'ᵀ.map h.fixedField.subtype = S'.map h.fixedField.subtype
    rw [Matrix.transpose_map, hS', hsym']
  have hdetcT : ∀ M : Matrix (Fin 4) (Fin 4) K, (cT h M).det = h.bar M.det := fun M => by
    rw [cT, Matrix.det_transpose]
    exact (RingHom.map_det (h.bar : K →+* K) M).symm
  have hdetS : S₀.det ≠ 0 := by
    rw [hS₀, Matrix.det_mul, hdetcT]
    exact mul_ne_zero ((map_ne_zero h.bar).2 hdet₀.ne_zero) hdet₀.ne_zero
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
  obtain ⟨Q', hQ'⟩ := GenLocL5Sign.exists_orthogonal_congr (ringChar_ne_two_of_odd hodd) S' hS'sym
  set Q : Matrix (Fin 4) (Fin 4) K := (Q' : Matrix (Fin 4) (Fin 4) h.fixedField).map h.fixedField.subtype with hQdef
  have hQbar : Q.map h.bar = Q := map_fixedField_bar h _
  have hcTQ : cT h Q = Qᵀ := by rw [cT, hQbar]
  have hdetQ : Q.det ≠ 0 := by
    have := RingHom.map_det h.fixedField.subtype (Q' : Matrix (Fin 4) (Fin 4) h.fixedField)
    rw [RingHom.mapMatrix_apply] at this
    rw [hQdef, ← this]
    intro h0
    have h1 : ((Q' : Matrix (Fin 4) (Fin 4) h.fixedField)).det = 0 := hι (by simpa using h0)
    exact ((Matrix.isUnit_iff_isUnit_det _).1 Q'.isUnit).ne_zero h1
  set D : Matrix (Fin 4) (Fin 4) K := Qᵀ * S₀ * Q with hD
  have hDeq : D = ((Q' : Matrix (Fin 4) (Fin 4) h.fixedField)ᵀ * S' * (Q' : Matrix (Fin 4) (Fin 4) h.fixedField)).map
      h.fixedField.subtype := by
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
    obtain ⟨c, hc⟩ := CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed hKcard hfix (inv_ne_zero (hd0 i))
    exact ⟨c, by rw [CFSG.LieType.BorelTits.unitaryInvolution_apply] at hc; exact hc⟩
  choose lam hlam using hlam
  have hlam0 : ∀ i, lam i ≠ 0 := by
    intro i h0
    have := hlam i
    rw [h0, mul_zero] at this
    exact inv_ne_zero (hd0 i) this.symm
  have hbar0 : ∀ i, h.bar (lam i) ≠ 0 := fun i => (map_ne_zero h.bar).2 (hlam0 i)
  set Lam : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal lam with hLam
  set P₂ : Matrix (Fin 4) (Fin 4) K := P₀ * Q * Lam with hP₂
  have hunit : cT h P₂ * P₂ = 1 := by
    have e1 : cT h P₂ * P₂ = cT h Lam * (Qᵀ * (cT h P₀ * P₀) * Q) * Lam := by
      rw [hP₂, cT_mul h (P₀ * Q) Lam, cT_mul h P₀ Q, hcTQ]
      simp only [Matrix.mul_assoc]
    rw [← hS₀] at e1
    rw [e1, ← hD, hDdiag, hLam, cT_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      have := hlam i
      have hd := hd0 i
      calc h.bar (lam i) * D i i * lam i = (h.bar (lam i) * lam i) * D i i := by ring
        _ = 1 := by rw [this]; exact inv_mul_cancel₀ hd
    · simp [hij]
  have hBP : B * P₂.map h.bar = P₂ * Matrix.diagonal (fun i => (lam i)⁻¹ * h.bar (lam i)) := by
    have e2 : P₂.map h.bar = P₀.map h.bar * Q * Lam.map h.bar := by
      rw [hP₂, Matrix.map_mul, Matrix.map_mul, hQbar]
    rw [e2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP₀, hP₂, Matrix.mul_assoc (P₀ * Q), hLam,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_map (map_zero _)]
    congr 2
    funext i
    rw [← mul_assoc, mul_inv_cancel₀ (hlam0 i), one_mul]
  refine ⟨P₂, fun i => (lam i)⁻¹ * h.bar (lam i), hunit, fun i => ?_, ?_⟩
  · rw [map_mul, map_inv₀, h.bar_bar]
    field_simp [hlam0 i, hbar0 i]
  · have e3 : P₂ * cT h P₂ = 1 := mul_eq_one_comm.mp hunit
    have e4 : P₂.map h.bar * P₂ᵀ = 1 := by
      have := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M.map h.bar) e3
      simp only [Matrix.map_mul, cT, Matrix.transpose_map, map_bar_bar h] at this
      rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
      exact this
    calc B = B * (P₂.map h.bar * P₂ᵀ) := by rw [e4, Matrix.mul_one]
      _ = (B * P₂.map h.bar) * P₂ᵀ := by rw [Matrix.mul_assoc]
      _ = _ := by rw [hBP]


theorem isUnitaryU_iff_cT (h : UnitaryFieldData p f K) (M : Matrix (Fin 4) (Fin 4) K) :
    GenLocU4Basic.IsUnitaryU (p ^ f) M ↔ cT h M * M = 1 := by
  unfold GenLocU4Basic.IsUnitaryU cT
  rw [GenLocU4Basic.bar_eq_pow h]

theorem exists_pm_omega [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f % 4 = 1) {ε : K} (hε : ε ^ (p ^ f + 1) = 1) :
    ∃ ω σ : K, ω ^ (p ^ f + 1) = 1 ∧ (σ = 1 ∨ σ = -1) ∧ ε = ω * ω * σ := by
  by_cases hs : GenLocU4ExtMu.IsSqM (p ^ f) ε
  · obtain ⟨ω, hω, hω2⟩ := hs
    exact ⟨ω, 1, hω, Or.inl rfl, by rw [hω2, mul_one]⟩
  · have h2 := GenLocU4ExtFrame.two_ne_zero_of_card hp hp2 hK
    have hm1 : (-1 : K) ^ (p ^ f + 1) = 1 := Even.neg_one_pow ⟨(p ^ f + 1) / 2, by omega⟩
    obtain ⟨ω, hω, hω2⟩ := GenLocU4ExtMu.isSqM_mul hp hp2 hK hm1 hε (GenLocU4ExtMu.not_isSqM_neg_one hq h2) hs
    exact ⟨ω, -1, hω, Or.inr rfl, by linear_combination hω2⟩


theorem exists_sym_nf_pm [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f % 4 = 1) {B : Matrix (Fin 4) (Fin 4) K} (hBt : Bᵀ = B)
    (hBU : GenLocU4Basic.IsUnitaryU (p ^ f) B) :
    ∃ (U : Matrix (Fin 4) (Fin 4) K) (σ : Fin 4 → K), GenLocU4Basic.IsUnitaryU (p ^ f) U ∧
      (∀ i, σ i = 1 ∨ σ i = -1) ∧ B = U * Matrix.diagonal σ * Uᵀ := by
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  obtain ⟨U₀, ε, hU₀, hε, hB⟩ := exists_sym_nf h hp2 hBt ((isUnitaryU_iff_cT h B).1 hBU)
  have hε' : ∀ i, ε i ^ (p ^ f + 1) = 1 := fun i => by
    have := hε i
    rw [UnitaryFieldData.bar_apply] at this
    rwa [pow_succ']
  choose ω σ hω hσ hεω using fun i => exists_pm_omega hp hp2 hK hq (hε' i)
  have hωb : ∀ i, h.bar (ω i) * ω i = 1 := fun i => by
    rw [UnitaryFieldData.bar_apply, ← pow_succ, hω i]
  refine ⟨U₀ * Matrix.diagonal ω, σ, ?_, hσ, ?_⟩
  · rw [isUnitaryU_iff_cT h, cT_mul, cT_diagonal]
    calc Matrix.diagonal (fun i => h.bar (ω i)) * cT h U₀ * (U₀ * Matrix.diagonal ω)
        = Matrix.diagonal (fun i => h.bar (ω i)) * (cT h U₀ * U₀) * Matrix.diagonal ω := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hU₀, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
          ext i j
          by_cases hij : i = j
          · subst hij; simp [hωb]
          · simp [hij]
  · rw [hB, Matrix.transpose_mul, Matrix.diagonal_transpose]
    have : Matrix.diagonal ε = Matrix.diagonal ω * Matrix.diagonal σ * Matrix.diagonal ω := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      rw [hεω i]; ring
    rw [this]
    simp only [Matrix.mul_assoc]


theorem wMat_eq : (wMat : Matrix (Fin 4) (Fin 4) K) = !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0] := by
  have e0 : (finSumFinEquiv.symm (0 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inl 0 := rfl
  have e1 : (finSumFinEquiv.symm (1 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inl 1 := rfl
  have e2 : (finSumFinEquiv.symm (2 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inr 0 := rfl
  have e3 : (finSumFinEquiv.symm (3 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inr 1 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, e4, e0, e1, e2, e3]

theorem blk4_eq_diag : blk4 (1 : Matrix (Fin 2) (Fin 2) K) ((-1 : K) • 1) = Matrix.diagonal ![1, 1, -1, -1] := by
  have e0 : (finSumFinEquiv.symm (0 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inl 0 := rfl
  have e1 : (finSumFinEquiv.symm (1 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inl 1 := rfl
  have e2 : (finSumFinEquiv.symm (2 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inr 0 := rfl
  have e3 : (finSumFinEquiv.symm (3 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inr 1 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk4, LinearFlag.diagBlock, Matrix.reindex_apply, Matrix.diagonal, e0, e1, e2, e3]

@[expose] def hypT (l m : K) : Matrix (Fin 4) (Fin 4) K :=
  !![l, 0, m, 0; 0, l, 0, m; l, 0, -m, 0; 0, l, 0, -m]

theorem hyp_unit (h : UnitaryFieldData p f K) (l m : K) (hl : 2 * h.bar l * l = 1) (hm : 2 * h.bar m * m = -1) :
    cT h (hypT l m) * (wMat : Matrix (Fin 4) (Fin 4) K) * hypT l m = 1 := by
  rw [wMat_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hypT, cT, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | linear_combination hl | linear_combination -hm

theorem hyp_intertwine (h : UnitaryFieldData p f K) (l m s : K) (hl : 2 * h.bar l * l = 1)
    (hm : 2 * h.bar m * m = -1) :
    hypT l m * ((2 * s * h.bar m * h.bar l) • (GenLocL4Out.m1 : Matrix (Fin 4) (Fin 4) K)) =
      s • (Matrix.diagonal ![1, 1, -1, -1] * (hypT l m).map h.bar) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hypT, GenLocL4Out.m1, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal, Matrix.smul_apply] <;>
    first | linear_combination (-s * h.bar l) * hm | linear_combination (s * h.bar m) * hl |
      linear_combination (s * h.bar l) * hm

theorem exists_two_inv_norm [Finite K] (h : UnitaryFieldData p f K) (c : K) (hc : h.bar c = c)
    (hc0 : c ≠ 0) : ∃ l : K, h.bar l * l = c := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card]; ring_nf
  have hfix : CFSG.LieType.BorelTits.unitaryInvolution K p f c = c := by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply]
    rw [UnitaryFieldData.bar_apply] at hc
    exact hc
  obtain ⟨l, hl⟩ := CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed hK hfix hc0
  exact ⟨l, by rw [CFSG.LieType.BorelTits.unitaryInvolution_apply] at hl; exact hl⟩

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher in
theorem exists_skew_nf [Finite K] (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) {B : Matrix (Fin 4) (Fin 4) K}
    (hBt : Bᵀ = -B) (hBU : cT h B * B = 1) :
    ∃ (U : Matrix (Fin 4) (Fin 4) K) (a : K), cT h U * U = 1 ∧
      B = U * (a • (GenLocL4Out.m1 : Matrix (Fin 4) (Fin 4) K)) * Uᵀ := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have hcT : cT h B = -(B.map h.bar) := by
    rw [cT, ← Matrix.transpose_map, hBt]
    ext i j; simp
  have hBB : B * B.map h.bar = -1 := by
    have h1 : (-(B.map h.bar)) * B = 1 := by rw [← hcT]; exact hBU
    have h3 : B * (-(B.map h.bar)) = 1 := mul_eq_one_comm.mp h1
    rw [Matrix.mul_neg] at h3
    exact neg_eq_iff_eq_neg.mp h3
  let g : GL (Fin 4) K := ⟨B, cT h B, mul_eq_one_comm.mp hBU, hBU⟩
  have hgg : (g : Matrix (Fin 4) (Fin 4) K) * (g : Matrix (Fin 4) (Fin 4) K).map h.bar = (-1 : K) • 1 := by
    rw [neg_one_smul]
    exact hBB
  obtain ⟨P, s, hs0, hPw, hBP⟩ := adapted_skew h hp2 (g := g) hBU hgg
  have hbar2 : h.bar (2 : K)⁻¹ = (2 : K)⁻¹ := by rw [map_inv₀]; congr 1; exact map_ofNat h.bar 2
  obtain ⟨l, hl⟩ := exists_two_inv_norm h (2 : K)⁻¹ hbar2 (inv_ne_zero h2)
  obtain ⟨m, hm⟩ := exists_two_inv_norm h (-(2 : K)⁻¹) (by rw [map_neg, hbar2]) (neg_ne_zero.2 (inv_ne_zero h2))
  have hl' : 2 * h.bar l * l = 1 := by
    calc 2 * h.bar l * l = 2 * (h.bar l * l) := by ring
      _ = 1 := by rw [hl]; exact mul_inv_cancel₀ h2
  have hm' : 2 * h.bar m * m = -1 := by
    calc 2 * h.bar m * m = 2 * (h.bar m * m) := by ring
      _ = -1 := by rw [hm]; field_simp
  refine ⟨(P : Matrix (Fin 4) (Fin 4) K) * hypT l m, 2 * s * h.bar m * h.bar l, ?_, ?_⟩
  · have e1 : cT h ((P : Matrix (Fin 4) (Fin 4) K) * hypT l m) * ((P : Matrix (Fin 4) (Fin 4) K) * hypT l m) =
        cT h (hypT l m) * (cT h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K)) * hypT l m := by
      rw [cT_mul]
      simp only [Matrix.mul_assoc]
    rw [e1, hPw]
    exact hyp_unit h l m hl' hm'
  · set U : Matrix (Fin 4) (Fin 4) K := (P : Matrix (Fin 4) (Fin 4) K) * hypT l m with hU
    have hunit : cT h U * U = 1 := by
      have e1 : cT h U * U = cT h (hypT l m) * (cT h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K)) * hypT l m := by
        rw [hU, cT_mul]
        simp only [Matrix.mul_assoc]
      rw [e1, hPw]
      exact hyp_unit h l m hl' hm'
    have e3 : U * cT h U = 1 := mul_eq_one_comm.mp hunit
    have e4 : U.map h.bar * Uᵀ = 1 := by
      have := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M.map h.bar) e3
      simp only [Matrix.map_mul, cT, Matrix.transpose_map, map_bar_bar h] at this
      rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
      exact this
    have e5 : B * U.map h.bar = U * ((2 * s * h.bar m * h.bar l) • (GenLocL4Out.m1 : Matrix (Fin 4) (Fin 4) K)) := by
      rw [hU, Matrix.map_mul, ← Matrix.mul_assoc, hBP, blk4_eq_diag, Matrix.mul_assoc, ← Matrix.mul_assoc (P : Matrix (Fin 4) (Fin 4) K),
        Matrix.mul_assoc (P : Matrix (Fin 4) (Fin 4) K), hyp_intertwine h l m s hl' hm']
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
    calc B = B * (U.map h.bar * Uᵀ) := by rw [e4, Matrix.mul_one]
      _ = (B * U.map h.bar) * Uᵀ := by rw [Matrix.mul_assoc]
      _ = _ := by rw [e5]

end GenLocU4OutFrame

end CFSG.GH74.Generic.BProg.B2
