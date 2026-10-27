module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutDaRot
public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutGenSu2b
public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutGenDb
public import CFSG.GH74.Generic.BProg.B2.GenLocU4Eich
public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutGenBase

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix
open scoped MatrixGroups
open GenLocU4Basic GenLocU4Out GenLocU4Gen CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary GenLocU4OutDaRot

namespace GenLocU4OutDaCore

section Generic

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem su_smul_def (g : SUid σ n) (v : Fin n → K) :
    g • v = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v := rfl

theorem tv_prod_identity (hσ : ∀ c, σ (σ c) = c) (u1 u2 : Fin n → K) (hu1 : herm σ u1 u1 = 0)
    (hu2 : herm σ u2 u2 = 0) (h12 : herm σ u1 u2 = 0) (h21 : herm σ u2 u1 = 0) (τ : K)
    (hp : herm σ (u1 + τ • u2) (u1 + τ • u2) = 0) (hm : herm σ (u1 + (-τ) • u2) (u1 + (-τ) • u2) = 0)
    (c c' : K) (hc : c + σ c = 0) (hc' : c' + σ c' = 0) (hc'' : (-2 * c') + σ (-2 * c') = 0)
    (hcc : 2 * c' * (σ τ * τ) = c) :
    tv hσ hu2 hc = tv hσ hp hc' * tv hσ hm hc' * tv hσ hu1 hc'' := by
  apply ext_smul
  intro x
  rw [mul_smul, mul_smul, tv_smul, tv_smul, tv_smul, tv_smul]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hu1, hu2, h12, h21, mul_zero,
    add_zero, smul_add, smul_smul, map_neg]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-(herm σ u2 x * u2 i)) * hcc

theorem tv_second_of_rotation (hσ : ∀ c, σ (σ c) = c) (h2 : (2 : K) ≠ 0) (Γ' : Subgroup (SUid σ n))
    (u1 u2 : Fin n → K) (hu1 : herm σ u1 u1 = 0) (hu2 : herm σ u2 u2 = 0)
    (h12 : herm σ u1 u2 = 0) (h21 : herm σ u2 u1 = 0)
    (g t : SUid σ n) (hg : g ∈ Γ') (ht : t ∈ Γ') (α β : K) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hgu : g • u1 = α • u1 + β • u2) (ht1 : t • u1 = u1) (ht2 : t • u2 = -u2)
    (hT1 : ∀ (c : K) (hc : c + σ c = 0), tv hσ hu1 hc ∈ Γ') (c : K) (hc : c + σ c = 0) :
    tv hσ hu2 hc ∈ Γ' := by
  obtain ⟨τ, hτ⟩ : ∃ τ : K, τ = β / α := ⟨_, rfl⟩
  have hτ0 : τ ≠ 0 := by rw [hτ]; exact div_ne_zero hβ hα
  have hστ : σ τ ≠ 0 := (map_ne_zero _).2 hτ0
  have hN : σ τ * τ ≠ 0 := mul_ne_zero hστ hτ0
  have hp : herm σ (u1 + τ • u2) (u1 + τ • u2) = 0 := by
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hu1, hu2, h12, h21,
      mul_zero, add_zero]
  have hm : herm σ (u1 + (-τ) • u2) (u1 + (-τ) • u2) = 0 := by
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hu1, hu2, h12, h21,
      mul_zero, add_zero]
  have hgu' : g • u1 = α • (u1 + τ • u2) := by
    rw [hgu, smul_add, smul_smul, hτ, mul_div_cancel₀ _ hα]
  have hlin : ∀ (g : SUid σ n) (a : K) (v : Fin n → K), g • (a • v) = a • (g • v) := by
    intro g a v
    simp only [su_smul_def, Matrix.mulVec_smul]
  have hvm : u1 + (-τ) • u2 = t • (u1 + τ • u2) := by
    have e : t • (u1 + τ • u2) = t • u1 + t • (τ • u2) := by
      simp only [su_smul_def, Matrix.mulVec_add]
    rw [e, ht1, hlin, ht2, smul_neg, neg_smul]
  have hTp : ∀ (c : K) (hc : c + σ c = 0), tv hσ hp hc ∈ Γ' := by
    intro c hc
    refine GenLocU4Aux.tv_mem_of_scalar hσ Γ' (u := g • u1) (a := u1 + τ • u2) α hα hgu' ?_ hp c hc
    intro hu0 c hc
    exact GenLocU4Aux.tv_conj_mem hσ Γ' hg hu1 hT1 rfl hu0 c hc
  have hTm : ∀ (c : K) (hc : c + σ c = 0), tv hσ hm hc ∈ Γ' := by
    intro c hc
    exact GenLocU4Aux.tv_conj_mem hσ Γ' ht hp hTp hvm hm c hc
  have hfix : σ (2 * (σ τ * τ)) = 2 * (σ τ * τ) := by
    rw [map_mul, map_mul, hσ, map_ofNat, mul_comm τ (σ τ)]
  have h2N : 2 * (σ τ * τ) ≠ 0 := mul_ne_zero h2 hN
  obtain ⟨c', hc'def⟩ : ∃ c' : K, c' = c / (2 * (σ τ * τ)) := ⟨_, rfl⟩
  have hc' : c' + σ c' = 0 := by
    rw [hc'def, map_div₀, hfix, ← add_div, hc, zero_div]
  have hc'' : (-2 * c') + σ (-2 * c') = 0 := by
    have : σ (-2 * c') = -2 * σ c' := by rw [map_mul, map_neg, map_ofNat]
    rw [this]
    linear_combination (-2 : K) * hc'
  have hcc : 2 * c' * (σ τ * τ) = c := by
    rw [hc'def]
    field_simp
  rw [tv_prod_identity hσ u1 u2 hu1 hu2 h12 h21 τ hp hm c c' hc hc' hc'' hcc]
  exact Γ'.mul_mem (Γ'.mul_mem (hTp c' hc') (hTm c' hc')) (hT1 _ hc'')

theorem herm_pair_iso {ε : K} (hε : ε * ε = -1) (hσε : σ ε = ε) :
    herm σ (![1, ε] : Fin 2 → K) ![1, ε] = 0 := by
  rw [herm_def, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_one, hσε]
  linear_combination hε

theorem herm_mixed_iso {ι κ : K} (hι : ι * ι = -1) (hσι : σ ι = ι) (hκ : κ + σ κ = 0) :
    herm σ (![1 + κ, ι * (1 - κ)] : Fin 2 → K) ![1 + κ, ι * (1 - κ)] = 0 ∧
      herm σ (![1 + κ, ι * (1 - κ), 0, 0] : Fin 4 → K) ![1 + κ, ι * (1 - κ), 0, 0] = 0 := by
  constructor
  · rw [herm_def, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_one, map_mul, map_sub, hσι]
    linear_combination 2 * hκ + ((1 - σ κ) * (1 - κ)) * hι
  · rw [herm_def, Fin.sum_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, map_add, map_one, map_mul, map_sub, map_zero, hσι]
    linear_combination 2 * hκ + ((1 - σ κ) * (1 - κ)) * hι

end Generic

section Blocks

variable {K : Type} [Field K] {p f : ℕ}

theorem blockMat4_zero_eq (Y : Matrix (Fin 2) (Fin 2) K) :
    blockMat 4 0 Y = !![Y 0 0, Y 0 1, 0, 0; Y 1 0, Y 1 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext i j
  rw [blockMat_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem fixIn_xi_block0 (Y : Matrix (Fin 2) (Fin 2) K) (h : !![0, 1; -1, 0] * Y = Y * !![0, 1; -1, 0]) :
    (xi : Matrix (Fin 4) (Fin 4) K) * blockMat 4 0 Y = blockMat 4 0 Y * xi := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [blockMat4_zero_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xi, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals first
    | linear_combination e00
    | linear_combination e01
    | linear_combination e10
    | linear_combination e11

theorem fixOut_B_block0 {q : ℕ} (hq0 : q ≠ 0) (c0 d0 c1 d1 : K) (Y : Matrix (Fin 2) (Fin 2) K)
    (h : !![c0, d0; d0, -c0] * Y.map (· ^ q) = Y * !![c0, d0; d0, -c0]) :
    bMat c0 d0 c1 d1 * (blockMat 4 0 Y).map (· ^ q) = blockMat 4 0 Y * bMat c0 d0 c1 d1 := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [blockMat4_zero_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bMat, Matrix.mul_apply, Fin.sum_univ_four, zero_pow hq0]
  all_goals first
    | linear_combination e00
    | linear_combination e01
    | linear_combination e10
    | linear_combination e11

theorem fixOut_Bxi_block0 {q : ℕ} (hq0 : q ≠ 0) (c0 d0 c1 d1 : K) (Y : Matrix (Fin 2) (Fin 2) K)
    (h : !![-d0, c0; c0, d0] * Y.map (· ^ q) = Y * !![-d0, c0; c0, d0]) :
    (bMat c0 d0 c1 d1 * xi) * (blockMat 4 0 Y).map (· ^ q) =
      blockMat 4 0 Y * (bMat c0 d0 c1 d1 * xi) := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [blockMat4_zero_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bMat, xi, Matrix.mul_apply, Fin.sum_univ_four, zero_pow hq0]
  all_goals first
    | linear_combination e00
    | linear_combination e01
    | linear_combination e10
    | linear_combination e11

theorem conj_bar_aux (R R' X J J' : Matrix (Fin 2) (Fin 2) K) (hJ : R * J = R') (hJJ : J * J' = 1)
    (hcomm : R' * X = X * R') : R * (J * X * J') = X * R := by
  calc R * (J * X * J') = (R * J) * X * J' := by simp only [Matrix.mul_assoc]
    _ = (R' * X) * J' := by rw [hJ]
    _ = (X * R') * J' := by rw [hcomm]
    _ = X * (R * J) * J' := by rw [hJ]
    _ = X * R * (J * J') := by simp only [Matrix.mul_assoc]
    _ = X * R := by rw [hJJ, Matrix.mul_one]

end Blocks

section Block0

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem block0_mem
    (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    {c0 d0 c1 d1 ι : K} (hι : ι * ι = -1) (hιq : ι ^ (p ^ f) = ι)
    (hU : IsUnitaryU (p ^ f) (bMat c0 d0 c1 d1)) (hmix : ∃ t : K, t * t = c0 + ι * d0)
    (Γ : Subgroup ↥(StatedSU 4 (p ^ f) K))
    (hP : (((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ *
      ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1)
    (h1 : ∀ g, FixIn (tT : Matrix (Fin 4) (Fin 4) K) g → FixIn (xi : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ)
    (h2 : ∀ g, FixOut (p ^ f) (bMat c0 d0 c1 d1) g → FixIn (tT : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ)
    (h6 : ∀ g, FixOut (p ^ f) (bMat c0 d0 c1 d1 * xi) g → FixIn (tT : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ) :
    ∀ x : Su K p f 2, GenLocU4Gen.frameBlock hK (1 : GL (Fin 4) K) hP 0 x ∈ Γ := by
  have hp : p.Prime := Fact.out
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have h2' : (2 : K) ≠ 0 := two_ne_zero_of_card hp hp2 hK
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq0 : p ^ f ≠ 0 := hodd.pos.ne'
  obtain ⟨hU00, hU01, -, -⟩ := bMat_unitary hU
  obtain ⟨t, ht⟩ := hmix
  have hbar := bar_add_mul h hιq
  have bb : ∀ x : K, (x ^ (p ^ f)) ^ (p ^ f) = x := fun x => h.bar_bar x
  have e0 : (c0 ^ (p ^ f) + ι * d0 ^ (p ^ f)) * (c0 - ι * d0) = 1 := by
    linear_combination hU00 - ι * hU01 - (d0 ^ (p ^ f) * d0) * hι
  have ht0 : t ≠ 0 := by
    rintro rfl
    have h0 : c0 + ι * d0 = 0 := by rw [← ht]; ring
    have h0' : c0 ^ (p ^ f) + ι * d0 ^ (p ^ f) = 0 := by rw [← hbar, h0]; exact zero_pow hq0
    rw [h0', zero_mul] at e0
    exact zero_ne_one e0
  have e1 : t ^ (p ^ f) * t ^ (p ^ f) = c0 ^ (p ^ f) + ι * d0 ^ (p ^ f) := by
    rw [← hbar, ← ht, mul_pow]
  have e2 : c0 * c0 + d0 * d0 = (c0 + ι * d0) * (c0 - ι * d0) := by
    linear_combination (d0 * d0) * hι
  have hts : t ^ (p ^ f) ≠ 0 := pow_ne_zero _ ht0
  obtain ⟨s, hs⟩ : ∃ s : K, s = t ^ (p ^ f) / t := ⟨_, rfl⟩
  have hs0 : s ≠ 0 := by rw [hs]; exact div_ne_zero hts ht0
  have hss : s ^ (p ^ f) * s = 1 := by
    rw [hs, div_pow, bb]
    field_simp
  have hs2 : s * s * (c0 * c0 + d0 * d0) = 1 := by
    rw [hs]
    field_simp
    linear_combination (c0 * c0 + d0 * d0) * e1 + (c0 ^ (p ^ f) + ι * d0 ^ (p ^ f)) * e2
      + (c0 + ι * d0) * e0 - ht
  have hB1J : (!![c0, d0; d0, -c0] : Matrix (Fin 2) (Fin 2) K) * !![0, 1; -1, 0] = !![-d0, c0; c0, d0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hMJ : (!![-d0, c0; c0, d0] : Matrix (Fin 2) (Fin 2) K) * !![0, 1; -1, 0] = !![-c0, -d0; -d0, c0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hJJ' : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) * !![0, -1; 1, 0] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hA0u : ((s • !![-d0, c0; c0, d0]).map (· ^ (p ^ f)))ᵀ * (s • !![-d0, c0; c0, d0]) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_pow, hodd.neg_pow] <;>
      first
      | linear_combination (c0 ^ (p ^ f) * c0 + d0 ^ (p ^ f) * d0) * hss + hU00
      | linear_combination (s ^ (p ^ f) * s) * hU01
      | linear_combination (-(s ^ (p ^ f) * s)) * hU01
  have hA0sq : (s • !![-d0, c0; c0, d0]) * (s • !![-d0, c0; c0, d0]) = (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination hs2 | ring1
  have hdet : (s • !![-d0, c0; c0, d0]).det = -1 := by
    rw [Matrix.det_smul, Matrix.det_fin_two]
    simp only [Fintype.card_fin, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val']
    linear_combination (-1 : K) * hs2
  have hA0det : ∀ lam : K, lam ^ (p ^ f) * lam = 1 → lam * lam ≠ (s • !![-d0, c0; c0, d0]).det := by
    intro lam hl hlam
    rw [hdet] at hlam
    have := GenLocU4ExtBd.pow_eq_self_of_sq_neg_one hq hlam
    rw [this, hlam] at hl
    exact h2' (by linear_combination -hl)
  have hNdet : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    simp [Matrix.det_fin_two]
  have hNu : ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K).map (· ^ (p ^ f)))ᵀ * !![0, 1; -1, 0] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, zero_pow hq0, hodd.neg_pow]
  have hNsq : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) * !![0, 1; -1, 0] = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hNs : ∀ lam : K, (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) ≠ lam • (1 : Matrix (Fin 2) (Fin 2) K) := by
    intro lam hl
    have := congrFun (congrFun hl 0) 1
    simp at this
  have hanti : (s • !![-d0, c0; c0, d0]) * !![0, 1; -1, 0] = -(!![0, 1; -1, 0] * (s • !![-d0, c0; c0, d0])) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hT0 : ∀ x : Su K p f 2, FixIn (tT : Matrix (Fin 4) (Fin 4) K)
      (GenLocU4Gen.frameBlock hK (1 : GL (Fin 4) K) hP 0 x) := fun x =>
    fixIn_block _ pmT 0 _ _ (coe_frameBlock_one hK hP 0 x) (Or.inl (by simp [GenLocU4Gen.idx4]))
  have hI : ∀ x : Su K p f 2, (s • !![-d0, c0; c0, d0]) * ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (s • !![-d0, c0; c0, d0]) →
      GenLocU4Gen.frameBlock hK (1 : GL (Fin 4) K) hP 0 x ∈ Γ := by
    intro x hx
    rw [Matrix.smul_mul, Matrix.mul_smul] at hx
    have hM := smul_right_injective _ hs0 hx
    refine h2 _ ?_ (hT0 x)
    unfold FixOut
    rw [coe_frameBlock_one hK hP 0 x]
    refine fixOut_B_block0 hq0 c0 d0 c1 d1 _ ?_
    rw [GenLocU4Gen.su2_map_bar x]
    exact conj_bar_aux _ _ _ _ _ hB1J hJJ' hM
  have hII : ∀ x : Su K p f 2, (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) *
      ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * !![0, 1; -1, 0] →
      GenLocU4Gen.frameBlock hK (1 : GL (Fin 4) K) hP 0 x ∈ Γ := by
    intro x hx
    refine h1 _ (hT0 x) ?_
    unfold FixIn
    rw [coe_frameBlock_one hK hP 0 x]
    exact fixIn_xi_block0 _ hx
  have hIII : ∀ x : Su K p f 2, ((s • !![-d0, c0; c0, d0]) * !![0, 1; -1, 0]) *
      ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * ((s • !![-d0, c0; c0, d0]) * !![0, 1; -1, 0]) →
      GenLocU4Gen.frameBlock hK (1 : GL (Fin 4) K) hP 0 x ∈ Γ := by
    intro x hx
    rw [Matrix.smul_mul, hMJ, Matrix.smul_mul, Matrix.mul_smul] at hx
    have hP1 := smul_right_injective _ hs0 hx
    refine h6 _ ?_ (hT0 x)
    unfold FixOut
    rw [coe_frameBlock_one hK hP 0 x]
    refine fixOut_Bxi_block0 hq0 c0 d0 c1 d1 _ ?_
    rw [GenLocU4Gen.su2_map_bar x]
    exact conj_bar_aux _ _ _ _ _ hMJ hJJ' hP1
  exact su2_gen_of_anti hp2 hK hq (GenLocU4Gen.frameBlock hK (1 : GL (Fin 4) K) hP 0) Γ
    (s • !![-d0, c0; c0, d0]) !![0, 1; -1, 0] hA0u hA0sq hA0det hNdet hNu hNsq hNs hanti hI hII hIII

end Block0

section Native

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem tv_block0_mem (hσ : IsUnitaryInvolution (unitaryInvolution K p f)) (Γ' : Subgroup (Su K p f 4))
    (hΓ0 : ∀ x : Su K p f 2, blockEmb2 K p f 3 0 x ∈ Γ') (a : Fin 2 → K)
    (ha : herm (unitaryInvolution K p f) a a = 0)
    (ha4 : herm (unitaryInvolution K p f) ![a 0, a 1, 0, 0] ![a 0, a 1, 0, 0] = 0)
    (c : K) (hc : c + unitaryInvolution K p f c = 0) : tv hσ.invol ha4 hc ∈ Γ' := by
  rw [← GenLocU4QSu4.blockEmb2_zero_eq_tv hσ.invol (tv hσ.invol ha hc) a c hc
    (fun y => tv_smul hσ.invol ha hc y) ha4]
  exact hΓ0 _

theorem isTransvU_mem (hK : Nat.card K = (p ^ f) ^ 2) (P : GL (Fin 4) K)
    (hP : ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1)
    (Γ : Subgroup ↥(StatedSU 4 (p ^ f) K)) (w : Fin 4 → K) (hw : herm (unitaryInvolution K p f) w w = 0)
    (hT : ∀ (c : K) (hc : c + unitaryInvolution K p f c = 0),
      tv (isUnitaryInvolution_unitaryInvolution hK).invol hw hc ∈ Γ.comap (frameConj (fieldData hK) P hP)) :
    ∀ g, IsTransvU (p ^ f) ((P : Matrix (Fin 4) (Fin 4) K) *ᵥ w) g → g ∈ Γ := by
  rintro g ⟨c, hc, hc0, hg⟩
  have hsig : ∀ x : K, unitaryInvolution K p f x = x ^ (p ^ f) :=
    fun x => unitaryInvolution_apply K p f x
  have hc' : c + unitaryInvolution K p f c = 0 := by rw [hsig]; exact hc
  have e : g = frameConj (fieldData hK) P hP
      (tv (isUnitaryInvolution_unitaryInvolution hK).invol hw hc') := by
    apply Subtype.ext
    apply Units.ext
    exact hg.trans (coe_frameConj_tv hK P hP w hw c hc').symm
  rw [e]
  exact hT c hc'

theorem coe_frameConj_one (hK : Nat.card K = (p ^ f) ^ 2)
    (hP : (((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ *
      ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1) (x : Su K p f 4) :
    (((frameConj (fieldData hK) (1 : GL (Fin 4) K) hP x : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  rw [coe_frameConj]
  simp

theorem tv_u2_mem (hσ : IsUnitaryInvolution (unitaryInvolution K p f)) (h2 : (2 : K) ≠ 0)
    (Γ' : Subgroup (Su K p f 4)) (hΓ0 : ∀ x : Su K p f 2, blockEmb2 K p f 3 0 x ∈ Γ') {ε : K}
    (hε : ε * ε = -1) (hσε : unitaryInvolution K p f ε = ε) (n' t' : Su K p f 4) (hn' : n' ∈ Γ')
    (ht' : t' ∈ Γ') (α β : K) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hnu : n' • (![1, ε, 0, 0] : Fin 4 → K) = α • ![1, ε, 0, 0] + β • ![0, 0, 1, ε])
    (ht1 : t' • (![1, ε, 0, 0] : Fin 4 → K) = ![1, ε, 0, 0])
    (ht2 : t' • (![0, 0, 1, ε] : Fin 4 → K) = -![0, 0, 1, ε]) :
    (∀ (c : K) (hc : c + unitaryInvolution K p f c = 0),
        tv hσ.invol (GenLocU4QSu4.herm_va hε hσε) hc ∈ Γ') ∧
      (∀ (c : K) (hc : c + unitaryInvolution K p f c = 0),
        tv hσ.invol (GenLocU4QSu4.herm_vb hε hσε) hc ∈ Γ') := by
  have hu1 := GenLocU4QSu4.herm_va hε hσε
  have hu2 := GenLocU4QSu4.herm_vb hε hσε
  have h12 : herm (unitaryInvolution K p f) (![1, ε, 0, 0] : Fin 4 → K) ![0, 0, 1, ε] = 0 := by
    simp [herm_def, Fin.sum_univ_four]
  have h21 : herm (unitaryInvolution K p f) (![0, 0, 1, ε] : Fin 4 → K) ![1, ε, 0, 0] = 0 := by
    simp [herm_def, Fin.sum_univ_four]
  have hae : herm (unitaryInvolution K p f) (![1, ε] : Fin 2 → K) ![1, ε] = 0 := herm_pair_iso hε hσε
  have hT1 : ∀ (c : K) (hc : c + unitaryInvolution K p f c = 0), tv hσ.invol hu1 hc ∈ Γ' :=
    fun c hc => tv_block0_mem hσ Γ' hΓ0 ![1, ε] hae hu1 c hc
  exact ⟨hT1, fun c hc => tv_second_of_rotation hσ.invol h2 Γ' _ _ hu1 hu2 h12 h21 n' t' hn' ht' α β
    hα hβ hnu ht1 ht2 hT1 c hc⟩

end Native

section NoFinite

variable {K : Type} [Field K]

theorem det_bMat (c0 d0 c1 d1 : K) :
    (bMat c0 d0 c1 d1).det = (c0 * c0 + d0 * d0) * (c1 * c1 + d1 * d1) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, bMat, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  ring

theorem sq_sum_mul_bar {ι c d : K} {q : ℕ} (hι : ι * ι = -1) (h1 : c ^ q * c + d ^ q * d = 1)
    (h2 : c ^ q * d - d ^ q * c = 0) :
    (c * c + d * d) * (c ^ q + ι * d ^ q) = c + ι * d ∧ (c ^ q + ι * d ^ q) * (c - ι * d) = 1 := by
  have e : (c ^ q + ι * d ^ q) * (c - ι * d) = 1 := by
    linear_combination h1 - ι * h2 - (d ^ q * d) * hι
  exact ⟨by linear_combination (c + ι * d) * e + (c ^ q + ι * d ^ q) * (d * d) * hι, e⟩

end NoFinite

section Minus

variable {K : Type} [Field K] [Finite K] {p f : ℕ}

theorem ne_zero_of_unitary_block (h : UnitaryFieldData p f K) {ι c d : K} (hι : ι * ι = -1)
    (hιq : ι ^ (p ^ f) = ι) (h1 : c ^ (p ^ f) * c + d ^ (p ^ f) * d = 1)
    (h2 : c ^ (p ^ f) * d - d ^ (p ^ f) * c = 0) : c + ι * d ≠ 0 := by
  have hq0 : p ^ f ≠ 0 := pow_ne_zero _ h.prime.ne_zero
  intro h0
  have h0' : c ^ (p ^ f) + ι * d ^ (p ^ f) = 0 := by
    rw [← bar_add_mul h hιq, h0]; exact zero_pow hq0
  have := (sq_sum_mul_bar hι h1 h2).2
  rw [h0', zero_mul] at this
  exact zero_ne_one this

theorem not_both_squares (h : UnitaryFieldData p f K) {c0 d0 c1 d1 ι : K} (hι : ι * ι = -1)
    (hιq : ι ^ (p ^ f) = ι) (hU : IsUnitaryU (p ^ f) (bMat c0 d0 c1 d1))
    (hM : ∀ μ : K, μ ^ (p ^ f + 1) = 1 → μ * μ ≠ (bMat c0 d0 c1 d1).det)
    {t ρ : K} (ht : t * t = c0 + ι * d0) (hρ : ρ * ρ = c1 + ι * d1) : False := by
  obtain ⟨hU00, hU01, hU22, hU23⟩ := bMat_unitary hU
  have hbar := bar_add_mul h hιq
  have bb : ∀ x : K, (x ^ (p ^ f)) ^ (p ^ f) = x := fun x => h.bar_bar x
  have hβ0 := ne_zero_of_unitary_block h hι hιq hU00 hU01
  have hβ1 := ne_zero_of_unitary_block h hι hιq hU22 hU23
  have ht0 : t ≠ 0 := by rintro rfl; exact hβ0 (by rw [← ht]; ring)
  have hρ0 : ρ ≠ 0 := by rintro rfl; exact hβ1 (by rw [← hρ]; ring)
  have htt : t ^ (p ^ f) * t ^ (p ^ f) = c0 ^ (p ^ f) + ι * d0 ^ (p ^ f) := by
    rw [← hbar, ← ht, mul_pow]
  have hρρ : ρ ^ (p ^ f) * ρ ^ (p ^ f) = c1 ^ (p ^ f) + ι * d1 ^ (p ^ f) := by
    rw [← hbar, ← hρ, mul_pow]
  have hts : t ^ (p ^ f) ≠ 0 := pow_ne_zero _ ht0
  have hρs : ρ ^ (p ^ f) ≠ 0 := pow_ne_zero _ hρ0
  have A : (c0 * c0 + d0 * d0) * (t ^ (p ^ f) * t ^ (p ^ f)) = c0 + ι * d0 := by
    rw [htt]; exact (sq_sum_mul_bar hι hU00 hU01).1
  have B : (c1 * c1 + d1 * d1) * (ρ ^ (p ^ f) * ρ ^ (p ^ f)) = c1 + ι * d1 := by
    rw [hρρ]; exact (sq_sum_mul_bar hι hU22 hU23).1
  refine hM ((t * ρ) / (t ^ (p ^ f) * ρ ^ (p ^ f))) ?_ ?_
  · rw [pow_succ, div_pow, mul_pow, mul_pow, bb, bb]
    field_simp
  · rw [det_bMat, div_mul_div_comm, div_eq_iff (mul_ne_zero (mul_ne_zero hts hρs) (mul_ne_zero hts hρs))]
    linear_combination (ρ * ρ) * ht + (c0 + ι * d0) * hρ - (c0 + ι * d0) * B
      - ((c1 * c1 + d1 * d1) * (ρ ^ (p ^ f) * ρ ^ (p ^ f))) * A

theorem mul_isSquare_of_nonsquares (hring : ringChar K ≠ 2) {x y : K} (hx : ¬ IsSquare x)
    (hy : ¬ IsSquare y) : IsSquare (x * y) := by
  have := Fintype.ofFinite K
  have hx0 : x ≠ 0 := fun h0 => hx ⟨0, by simp [h0]⟩
  have hy0 : y ≠ 0 := fun h0 => hy ⟨0, by simp [h0]⟩
  have hxN : x ^ (Fintype.card K / 2) = -1 := by
    rcases FiniteField.pow_dichotomy hring hx0 with h | h
    · exact absurd ((FiniteField.isSquare_iff hring hx0).2 h) hx
    · exact h
  have hyN : y ^ (Fintype.card K / 2) = -1 := by
    rcases FiniteField.pow_dichotomy hring hy0 with h | h
    · exact absurd ((FiniteField.isSquare_iff hring hy0).2 h) hy
    · exact h
  rw [FiniteField.isSquare_iff hring (mul_ne_zero hx0 hy0), mul_pow, hxN, hyN]
  norm_num

theorem not_both_nonsquares (h : UnitaryFieldData p f K) {c0 d0 c1 d1 ι : K} (hι : ι * ι = -1)
    (hιq : ι ^ (p ^ f) = ι) (hU : IsUnitaryU (p ^ f) (bMat c0 d0 c1 d1))
    (hM : ∀ μ : K, μ ^ (p ^ f + 1) = 1 → μ * μ ≠ (bMat c0 d0 c1 d1).det)
    {ρ : K} (hρ : ρ * ρ = (c0 + ι * d0) * (c1 + ι * d1)) : False := by
  obtain ⟨hU00, hU01, hU22, hU23⟩ := bMat_unitary hU
  have hbar := bar_add_mul h hιq
  have bb : ∀ x : K, (x ^ (p ^ f)) ^ (p ^ f) = x := fun x => h.bar_bar x
  have hβ0 := ne_zero_of_unitary_block h hι hιq hU00 hU01
  have hβ1 := ne_zero_of_unitary_block h hι hιq hU22 hU23
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    have : (c0 + ι * d0) * (c1 + ι * d1) = 0 := by rw [← hρ]; ring
    exact mul_ne_zero hβ0 hβ1 this
  have hρρ : ρ ^ (p ^ f) * ρ ^ (p ^ f) =
      (c0 ^ (p ^ f) + ι * d0 ^ (p ^ f)) * (c1 ^ (p ^ f) + ι * d1 ^ (p ^ f)) := by
    rw [← mul_pow, hρ, mul_pow, hbar, hbar]
  have hρs : ρ ^ (p ^ f) ≠ 0 := pow_ne_zero _ hρ0
  have A := (sq_sum_mul_bar hι hU00 hU01).1
  have B := (sq_sum_mul_bar hι hU22 hU23).1
  refine hM (ρ / ρ ^ (p ^ f)) ?_ ?_
  · rw [pow_succ, div_pow, bb]
    field_simp
  · rw [det_bMat, div_mul_div_comm, div_eq_iff (mul_ne_zero hρs hρs), hρ, hρρ]
    linear_combination (-(c0 + ι * d0)) * B
      - ((c1 * c1 + d1 * d1) * (c1 ^ (p ^ f) + ι * d1 ^ (p ^ f))) * A

end Minus

end GenLocU4OutDaCore

namespace GenLocU4OutDa

open GenLocU4OutDaCore

variable {K : Type} [Field K] {p f : ℕ} [Finite K]

theorem outDa_core
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    (B : Matrix (Fin 4) (Fin 4) K) (hBU : IsUnitaryU (p ^ f) B) (hBm : IsMinusU (p ^ f) B)
    (htB : tT * B = B * tT) (hxiB : xi * B = -(B * xi)) {ι : K} (hι : ι * ι = -1) (hιq : ι ^ (p ^ f) = ι)
    (hmix : ∃ t : K, t * t = B 0 0 + ι * B 0 1) (Γ : Subgroup ↥(StatedSU 4 (p ^ f) K))
    (h1 : ∀ g, FixIn (tT : Matrix (Fin 4) (Fin 4) K) g → FixIn (xi : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ)
    (h2 : ∀ g, FixOut (p ^ f) B g → FixIn (tT : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ)
    (h3 : ∀ g, FixOut (p ^ f) B g → FixIn (xi : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ)
    (h6 : ∀ g, FixOut (p ^ f) (B * xi) g → FixIn (tT : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ) : Γ = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have h2' : (2 : K) ≠ 0 := two_ne_zero_of_card hp hp2 hK
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq0 : p ^ f ≠ 0 := hodd.pos.ne'
  have hP : (((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ *
      ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    simp [Matrix.map_one, zero_pow hq0]
  have hBs : Bᵀ = B := hBm.1
  have hBd := hBm.2
  obtain ⟨c0, d0, c1, d1, hB⟩ : ∃ c0 d0 c1 d1 : K, B = bMat c0 d0 c1 d1 :=
    ⟨_, _, _, _, B_shape h2' htB hxiB⟩
  subst hB
  have hmix' : ∃ t : K, t * t = c0 + ι * d0 := by simpa [bMat] using hmix
  have h0 := block0_mem hp2 hK hq hι hιq hBU hmix' Γ hP h1 h2 h6
  obtain ⟨hU00, hU01, hU22, hU23⟩ := bMat_unitary hBU
  obtain ⟨t, ht⟩ := hmix'
  have hbar := bar_add_mul h hιq
  have bb : ∀ x : K, (x ^ (p ^ f)) ^ (p ^ f) = x := fun x => h.bar_bar x
  have e0 : (c0 ^ (p ^ f) + ι * d0 ^ (p ^ f)) * (c0 - ι * d0) = 1 := by
    linear_combination hU00 - ι * hU01 - (d0 ^ (p ^ f) * d0) * hι
  have hu0 : c0 ^ (p ^ f) + ι * d0 ^ (p ^ f) ≠ 0 := left_ne_zero_of_mul_eq_one e0
  obtain ⟨σ, hσdef⟩ : ∃ σ : K, σ = (c1 ^ (p ^ f) + ι * d1 ^ (p ^ f)) / (c0 ^ (p ^ f) + ι * d0 ^ (p ^ f)) :=
    ⟨_, rfl⟩
  have hσrel : σ * (c0 + ι * d0) ^ (p ^ f) = (c1 + ι * d1) ^ (p ^ f) := by
    rw [hbar, hbar, hσdef]
    field_simp
  have hF1 : σ ^ (p ^ f) * (c0 + ι * d0) = c1 + ι * d1 := by
    have := congrArg (fun x : K => x ^ (p ^ f)) hσrel
    simp only [mul_pow] at this
    rwa [bb, bb] at this
  have hσns : ∀ r : K, r * r ≠ σ := by
    intro r hr
    refine not_both_squares h hι hιq hBU hBd (t := t) (ρ := r ^ (p ^ f) * t) ht ?_
    calc (r ^ (p ^ f) * t) * (r ^ (p ^ f) * t) = (r * r) ^ (p ^ f) * (t * t) := by rw [mul_pow]; ring
      _ = σ ^ (p ^ f) * (c0 + ι * d0) := by rw [hr, ht]
      _ = c1 + ι * d1 := hF1
  have hσ0 : σ ≠ 0 := fun h0 => hσns 0 (by rw [h0]; ring)
  obtain ⟨a, b, hab, hb0, ha2⟩ := exists_rot_param hp hp2 hK hq hσns
  obtain ⟨hnU, hndet, hnxi, hna, hnb⟩ := daRot_mem hp hp2 hK hι hιq hab
  have hσ' : σ * ((bMat c0 d0 c1 d1) 0 0 + ι * (bMat c0 d0 c1 d1) 0 1) ^ (p ^ f) =
      ((bMat c0 d0 c1 d1) 2 2 + ι * (bMat c0 d0 c1 d1) 2 3) ^ (p ^ f) := by
    simpa [bMat] using hσrel
  have hnfix := daRot_fixOut hp hp2 hK hι hιq hab (bMat c0 d0 c1 d1) hBU hBs htB hxiB hσ'
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha2 (by simp [zero_pow hq0])
  have haq0 : a ^ (p ^ f) ≠ 0 := pow_ne_zero _ ha0
  have hbq0 : b ^ (p ^ f) ≠ 0 := pow_ne_zero _ hb0
  have hσq0 : σ ^ (p ^ f) ≠ 0 := pow_ne_zero _ hσ0
  obtain ⟨nS, hnS⟩ : ∃ nS : ↥(StatedSU 4 (p ^ f) K),
      ((nS : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = daRot (p ^ f) ι a b σ :=
    ⟨suOf (p ^ f) _ hnU hndet, coe_suOf _ _ hnU hndet⟩
  have hTU : IsUnitaryU (p ^ f) (tT : Matrix (Fin 4) (Fin 4) K) := by
    unfold IsUnitaryU
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [tT, Matrix.diagonal, Matrix.mul_apply, hodd.neg_pow, zero_pow hq0]
  have hTdet : (tT : Matrix (Fin 4) (Fin 4) K).det = 1 := by
    simp [tT, Matrix.det_diagonal, Fin.prod_univ_four]
  obtain ⟨tS, htS⟩ : ∃ tS : ↥(StatedSU 4 (p ^ f) K),
      ((tS : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = tT :=
    ⟨suOf (p ^ f) _ hTU hTdet, coe_suOf _ _ hTU hTdet⟩
  have hxiT : (xi : Matrix (Fin 4) (Fin 4) K) * tT = tT * xi := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [tT, xi, Matrix.mul_apply, Matrix.diagonal]
  have hnΓ : nS ∈ Γ := h3 nS (by unfold FixOut; rw [hnS]; exact hnfix)
    (by unfold FixIn; rw [hnS]; exact hnxi.symm)
  have htΓ : tS ∈ Γ := h1 tS (by unfold FixIn; rw [htS]) (by unfold FixIn; rw [htS]; exact hxiT)
  have hσ := isUnitaryInvolution_unitaryInvolution (K := K) (p := p) (f := f) hK
  have hΓ0 : ∀ x : Su K p f 2,
      blockEmb2 K p f 3 0 x ∈ Γ.comap (frameConj (fieldData hK) (1 : GL (Fin 4) K) hP) := fun x => h0 x
  obtain ⟨n', hn'⟩ := frameConj_surjective (fieldData hK) (1 : GL (Fin 4) K) hP nS
  obtain ⟨t', ht'⟩ := frameConj_surjective (fieldData hK) (1 : GL (Fin 4) K) hP tS
  have hn'Γ : n' ∈ Γ.comap (frameConj (fieldData hK) (1 : GL (Fin 4) K) hP) := by
    show frameConj (fieldData hK) (1 : GL (Fin 4) K) hP n' ∈ Γ
    rw [hn']; exact hnΓ
  have ht'Γ : t' ∈ Γ.comap (frameConj (fieldData hK) (1 : GL (Fin 4) K) hP) := by
    show frameConj (fieldData hK) (1 : GL (Fin 4) K) hP t' ∈ Γ
    rw [ht']; exact htΓ
  have hn'mat : ((n' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = daRot (p ^ f) ι a b σ := by
    rw [← coe_frameConj_one hK hP n', hn', hnS]
  have ht'mat : ((t' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = tT := by
    rw [← coe_frameConj_one hK hP t', ht', htS]
  have hσι : ∀ ε : K, ε ^ (p ^ f) = ε → unitaryInvolution K p f ε = ε := fun ε hε => by
    rw [unitaryInvolution_apply]; exact hε
  have hmιq : (-ι) ^ (p ^ f) = -ι := by rw [hodd.neg_pow, hιq]
  have hmι : (-ι) * (-ι) = -1 := by linear_combination hι
  have htact : ∀ ε : K, t' • (![1, ε, 0, 0] : Fin 4 → K) = ![1, ε, 0, 0] ∧
      t' • (![0, 0, 1, ε] : Fin 4 → K) = -![0, 0, 1, ε] := by
    intro ε
    rw [su_smul_def, su_smul_def, ht'mat]
    constructor <;> ext i <;> fin_cases i <;>
      simp [tT, Matrix.mulVec, dotProduct, Matrix.diagonal]
  have hres_ι := tv_u2_mem hσ h2' _ hΓ0 hι (hσι ι hιq) n' t' hn'Γ ht'Γ a b ha0 hb0
    (by rw [su_smul_def, hn'mat]; exact hna) (htact ι).1 (htact ι).2
  have hres_mι := tv_u2_mem hσ h2' _ hΓ0 hmι (hσι (-ι) hmιq) n' t' hn'Γ ht'Γ (a ^ (p ^ f))
    (σ ^ (p ^ f) * b ^ (p ^ f)) haq0 (mul_ne_zero hσq0 hbq0)
    (by rw [su_smul_def, hn'mat]; exact hnb) (htact (-ι)).1 (htact (-ι)).2
  obtain ⟨κ, hκ0, hκ⟩ := hσ.exists_traceZero
  have hκq : κ ^ (p ^ f) = -κ := by
    have := hκ
    rw [unitaryInvolution_apply] at this
    linear_combination this
  obtain ⟨hae, hw0iso⟩ := herm_mixed_iso hι (hσι ι hιq) hκ
  have hTw0 : ∀ (c : K) (hc : c + unitaryInvolution K p f c = 0), tv hσ.invol hw0iso hc ∈
      Γ.comap (frameConj (fieldData hK) (1 : GL (Fin 4) K) hP) :=
    fun c hc => tv_block0_mem hσ _ hΓ0 ![1 + κ, ι * (1 - κ)] hae hw0iso c hc
  obtain ⟨v, hvdef⟩ : ∃ v : Fin 4 → K, v = n' • (![1 + κ, ι * (1 - κ), 0, 0] : Fin 4 → K) := ⟨_, rfl⟩
  have hviso : herm (unitaryInvolution K p f) v v = 0 := by
    rw [hvdef, herm_smul_smul]; exact hw0iso
  have hTv' : ∀ (c : K) (hc : c + unitaryInvolution K p f c = 0), tv hσ.invol hviso hc ∈
      Γ.comap (frameConj (fieldData hK) (1 : GL (Fin 4) K) hP) :=
    fun c hc => GenLocU4Aux.tv_conj_mem hσ.invol _ hn'Γ hw0iso hTw0 hvdef hviso c hc
  have hw0 : (![1 + κ, ι * (1 - κ), 0, 0] : Fin 4 → K) = ![1, ι, 0, 0] + κ • ![1, -ι, 0, 0] := by
    ext i
    fin_cases i <;> simp
    ring
  have hveq : v = (a • ![1, ι, 0, 0] + b • ![0, 0, 1, ι]) +
      κ • (a ^ (p ^ f) • ![1, -ι, 0, 0] + (σ ^ (p ^ f) * b ^ (p ^ f)) • ![0, 0, 1, -ι]) := by
    rw [hvdef, su_smul_def, hn'mat, hw0, Matrix.mulVec_add, Matrix.mulVec_smul, hna, hnb]
  have hv0 : v 0 = a + κ * a ^ (p ^ f) := by rw [hveq]; simp
  have hv1 : v 1 = ι * (a - κ * a ^ (p ^ f)) := by rw [hveq]; simp; ring
  have hbaradd : ∀ x y : K, (x + y) ^ (p ^ f) = x ^ (p ^ f) + y ^ (p ^ f) :=
    fun x y => map_add h.bar x y
  have hbarsub : ∀ x y : K, (x - y) ^ (p ^ f) = x ^ (p ^ f) - y ^ (p ^ f) :=
    fun x y => map_sub h.bar x y
  have hv01 : (v 0) ^ (p ^ f) * v 0 + (v 1) ^ (p ^ f) * v 1 ≠ 0 := by
    have e1 : (a + κ * a ^ (p ^ f)) ^ (p ^ f) = a ^ (p ^ f) + (-κ) * a := by
      rw [hbaradd, mul_pow, bb, hκq]
    have e2 : (ι * (a - κ * a ^ (p ^ f))) ^ (p ^ f) = ι * (a ^ (p ^ f) - (-κ) * a) := by
      rw [mul_pow, hbarsub, mul_pow, bb, hκq, hιq]
    have key : (v 0) ^ (p ^ f) * v 0 + (v 1) ^ (p ^ f) * v 1 =
        2 * κ * (a ^ (p ^ f) * a ^ (p ^ f) - a * a) := by
      rw [hv0, hv1, e1, e2]
      linear_combination ((a ^ (p ^ f) + κ * a) * (a - κ * a ^ (p ^ f))) * hι
    rw [key]
    refine mul_ne_zero (mul_ne_zero h2' hκ0) (sub_ne_zero.2 fun he => ha2 ?_)
    rw [mul_pow]
    exact he
  have hv : ∑ i, (v i) ^ (p ^ f) * v i = 0 := by
    have := hviso
    rw [herm_def] at this
    simpa only [unitaryInvolution_apply] using this
  have hβ : ι ^ (p ^ f) * ι = -1 := by rw [hιq]; exact hι
  have hTv : ∀ g, IsTransvU (p ^ f) (((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v) g → g ∈ Γ :=
    isTransvU_mem hK 1 hP Γ v hviso hTv'
  have hTall : ∀ w : Fin 4 → K,
      (w = ![1, ι, 0, 0] ∨ w = ![1, -ι, 0, 0] ∨ w = ![0, 0, 1, ι] ∨ w = ![0, 0, 1, -ι]) →
      ∀ g, IsTransvU (p ^ f) (((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ w) g → g ∈ Γ := by
    rintro w (rfl | rfl | rfl | rfl)
    · exact isTransvU_mem hK 1 hP Γ _ (GenLocU4QSu4.herm_va hι (hσι ι hιq)) hres_ι.1
    · exact isTransvU_mem hK 1 hP Γ _ (GenLocU4QSu4.herm_va hmι (hσι (-ι) hmιq)) hres_mι.1
    · exact isTransvU_mem hK 1 hP Γ _ (GenLocU4QSu4.herm_vb hι (hσι ι hιq)) hres_ι.2
    · exact isTransvU_mem hK 1 hP Γ _ (GenLocU4QSu4.herm_vb hmι (hσι (-ι) hmιq)) hres_mι.2
  exact GenLocU4Eich.su4_eq_top_of_tv_frame hp hp2 hK Γ 1 hP ι ι hβ hβ hTall v hv hv01 hTv

end GenLocU4OutDa

end CFSG.GH74.Generic.BProg.B2
