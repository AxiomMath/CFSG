module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M1Gam
public import Mathlib.FieldTheory.Finite.Extension

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (xBlock yBlock zBlock)

local notation "actΓ" => CFSG.RankThree.PartOne.U5K.Hyp.act

section Frobenius

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_forall_eq_pow_two_pow (σ : K ≃+* K) : ∃ j : ℕ, ∀ x : K, σ x = x ^ 2 ^ j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  let g : K ≃ₐ[ZMod 2] K := AlgEquiv.ofRingEquiv (f := σ) fun x =>
    congrArg (fun f : ZMod 2 →+* K => f x)
      (Subsingleton.elim (σ.toRingHom.comp (algebraMap (ZMod 2) K)) (algebraMap (ZMod 2) K))
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod 2) 2 K g
  refine ⟨i, fun x => ?_⟩
  have := hi x
  rw [Nat.card_zmod] at this
  exact this

end Frobenius

section Model

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem not_dvd_five_mul (hf : 3 ≤ f) {j : ℕ} (hj0 : 0 < j) (hj : j < 2 * f) :
    ¬ (2 ^ f) ^ 2 - 1 ∣ 5 * 2 ^ j - 5 := by
  intro hdvd
  have hQ8 : 8 ≤ 2 ^ f :=
    (Nat.pow_le_pow_right (by norm_num) hf).trans_eq' (by norm_num)
  have hP2 : 2 ≤ 2 ^ j :=
    (Nat.pow_le_pow_right (by norm_num) hj0).trans_eq' (by norm_num)
  have hQQ : 8 * 2 ^ f ≤ (2 ^ f) ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul_right _ hQ8
  rcases le_or_gt j f with hjf | hjf
  ·
    have hPQ : 2 ^ j ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hjf
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega
  ·
    obtain ⟨d, rfl⟩ : ∃ d, j = f + d := ⟨j - f, by omega⟩
    have hR2 : 2 ≤ 2 ^ d :=
      (Nat.pow_le_pow_right (by norm_num) (show 1 ≤ d by omega)).trans_eq' (by norm_num)
    have hRQ : 2 ^ d < 2 ^ f := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [pow_add] at hdvd
    obtain ⟨m, hm⟩ := hdvd
    set Q := 2 ^ f with hQ
    set R := 2 ^ d with hR
    have hQR : 5 ≤ 5 * (Q * R) := by nlinarith
    have hQ1 : 1 ≤ Q ^ 2 := by nlinarith
    have hm' : (5 * (Q * R) : ℤ) - 5 = ((Q : ℤ) ^ 2 - 1) * m := by
      have := congrArg (fun n : ℕ => (n : ℤ)) hm
      push_cast [Nat.cast_sub hQR, Nat.cast_sub hQ1] at this
      linear_combination this
    have hQ8' : (8 : ℤ) ≤ Q := by exact_mod_cast hQ8
    have hR2' : (2 : ℤ) ≤ R := by exact_mod_cast hR2
    have hRQ' : (R : ℤ) + 1 ≤ Q := by exact_mod_cast hRQ
    have hm1 : (1 : ℤ) ≤ m := by
      by_contra hcon
      have hm0 : (m : ℤ) = 0 := by have := Int.natCast_nonneg m; omega
      rw [hm0, mul_zero] at hm'
      nlinarith
    have hm4 : (m : ℤ) ≤ 4 := by
      by_contra hcon
      have h5 : (5 : ℤ) ≤ m := by omega
      nlinarith [mul_le_mul_of_nonneg_left h5 (show (0 : ℤ) ≤ (Q : ℤ) ^ 2 - 1 by nlinarith),
        mul_le_mul_of_nonneg_left hRQ' (show (0 : ℤ) ≤ Q by omega)]
    have hk : (Q : ℤ) * (5 * R - m * Q) = 5 - m := by linear_combination hm'
    rcases le_or_gt (5 * (R : ℤ) - m * Q) 0 with hk0 | hk0
    · nlinarith [mul_le_mul_of_nonneg_left hk0 (show (0 : ℤ) ≤ Q by omega)]
    · have hk1 : (1 : ℤ) ≤ 5 * R - m * Q := by omega
      nlinarith [mul_le_mul_of_nonneg_left hk1 (show (0 : ℤ) ≤ Q by omega)]

theorem ringEquiv_eq_one_of_fixes (h : UnitaryFieldData 2 f K) (hf : 3 ≤ f) {ω : Kˣ}
    (hω : orderOf ω = (2 ^ f) ^ 2 - 1) {σ : K ≃+* K} (hσ : σ ((ω : K) ^ 5) = (ω : K) ^ 5) :
    σ = 1 := by
  have := h.charP
  have := h.finite
  obtain ⟨j, hj⟩ := exists_forall_eq_pow_two_pow σ
  have hcard : ∀ x : K, x ^ ((2 ^ f) ^ 2) = x := fun x => by
    have := Fintype.ofFinite K
    rw [← h.card_eq_sq, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  have hiter : ∀ (m : ℕ) (x : K), x ^ (((2 ^ f) ^ 2) ^ m) = x := by
    intro m x
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_mul, ih, hcard]
  have hσ' : ∀ x : K, σ x = x ^ 2 ^ (j % (2 * f)) := fun x => by
    have e : 2 ^ j = 2 ^ (j % (2 * f)) * ((2 ^ f) ^ 2) ^ (j / (2 * f)) := by
      calc 2 ^ j = 2 ^ (j % (2 * f) + 2 * f * (j / (2 * f))) := by rw [Nat.mod_add_div]
        _ = 2 ^ (j % (2 * f)) * (2 ^ (2 * f)) ^ (j / (2 * f)) := by rw [pow_add, pow_mul]
        _ = 2 ^ (j % (2 * f)) * ((2 ^ f) ^ 2) ^ (j / (2 * f)) := by
          rw [← pow_mul 2 f 2, mul_comm f 2]
    rw [hj x, e, pow_mul, hiter]
  have hlt : j % (2 * f) < 2 * f := Nat.mod_lt _ (by omega)
  rcases Nat.eq_zero_or_pos (j % (2 * f)) with h0 | hpos
  · ext x
    rw [hσ' x, h0, pow_zero, pow_one]
    rfl
  exfalso
  have hu : ω ^ (5 * 2 ^ (j % (2 * f))) = ω ^ 5 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_mul, ← hσ', hσ])
  have h5 : 5 ≤ 5 * 2 ^ (j % (2 * f)) := by
    have : 1 ≤ 2 ^ (j % (2 * f)) := Nat.one_le_two_pow
    omega
  have h1 : ω ^ (5 * 2 ^ (j % (2 * f)) - 5) = 1 := by
    rw [pow_sub ω h5, hu, mul_inv_cancel]
  have hdvd := orderOf_dvd_of_pow_eq_one h1
  rw [hω] at hdvd
  exact not_dvd_five_mul hf hpos hlt hdvd

theorem xBlock_mul_of_col {P Q : Matrix (HypIndex 2 1) (HypIndex 2 1) K}
    (hQ : ∀ (k : Fin 1 ⊕ Fin 2) (j : Fin 2), Q (.inr k) (.inl j) = 0) :
    xBlock (P * Q) = xBlock P * xBlock Q := by
  ext i j
  simp [xBlock, Matrix.mul_apply, Fintype.sum_sum_type, hQ]

theorem xBlock_mat_leviSU (C : SpecialLinearGroup (Fin 2) K) :
    xBlock (mat (UnitaryHigher.leviSU h 1 C)) = C := by
  ext i j
  rw [mat_leviSU]
  rfl

theorem exists_N₁_of_sq (hf : 3 ≤ f) {x : Gam h}
    (hI : ∀ i ∈ I₁sub h, ∃ s ∈ hypScalars h 2 1, actΓ h x i = s * i)
    (hI' : ∀ i ∈ I₁sub h, ∃ s ∈ hypScalars h 2 1, actΓ h (x * x) i = s * i) :
    ∃ g ∈ N₁sub h, ∀ n ∈ N₁sub h, actΓ h (x * x) n = g * n * g⁻¹ := by
  have := h.charP
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf2 : 2 ≤ f := by omega
  set y := x * x with hy
  obtain ⟨j, hj, β, -, hβ, -, e1, e2, e3, e4, e5⟩ := exists_I₁_fifth (h := h) hf2
  have ht : j ^ 5 ∈ hypTorus h 2 1 := pow_mem (torusEq_le _ hj) 5
  have hfixx : actΓ h x (j ^ 5) = j ^ 5 := by
    obtain ⟨s, hs, hjs⟩ := hI j hj
    exact act_pow_five_eq hs hjs
  have hfixy : actΓ h y (j ^ 5) = j ^ 5 := by
    obtain ⟨s, hs, hjs⟩ := hI' j hj
    exact act_pow_five_eq hs hjs
  have hσx : x.1.right β = β ∨ x.1.right β = β⁻¹ := by
    rcases (lmat_blocks_of_fixed ht hfixx hβ e1 e2 e3 e4 e5).2 with h1 | h1
    · exact Or.inl h1.1
    · exact Or.inr h1.1
  have hyr : y.1.right = x.1.right * x.1.right := by
    rw [hy, Subgroup.coe_mul, SemidirectProduct.mul_right]
  have hσy : y.1.right β = β := by
    rw [hyr]
    show x.1.right (x.1.right β) = β
    rcases hσx with e | e
    · rw [e, e]
    · rw [e, map_inv₀, e, inv_inv]
  obtain ⟨hz, hcase⟩ := lmat_blocks_of_fixed ht hfixy hβ e1 e2 e3 e4 e5
  have hEF : ∀ i j : Fin 2, lmat y (.inl i) (.inr (.inr j)) = 0 ∧
      lmat y (.inr (.inr i)) (.inl j) = 0 := by
    rcases hcase with h1 | h1
    · exact h1.2
    · exact absurd (hσy.symm.trans h1.1) hβ
  obtain ⟨ω, hω⟩ := exists_unit_generator h
  obtain ⟨i, hi, i1, i2, -, -, -⟩ := exists_torus h ω.ne_zero ω.ne_zero
  have hiI : i ∈ I₁sub h := mem_I₁sub.2 ⟨hi, i1.trans i2.symm⟩
  have hfixi : actΓ h y (i ^ 5) = i ^ 5 := by
    obtain ⟨s, hs, his⟩ := hI' i hiI
    exact act_pow_five_eq hs his
  have hti : i ^ 5 ∈ hypTorus h 2 1 := pow_mem hi 5
  have hent := lmat_entry_of_act_torus hti hfixi
  have hiE : ∀ k : Fin 2, mat (i ^ 5) (.inl k) (.inl k) = (ω : K) ^ 5 := fun k => by
    rw [torus_pow_apply hi]
    fin_cases k
    · exact congrArg (· ^ 5) i1
    · exact congrArg (· ^ 5) i2
  have hσω : y.1.right ((ω : K) ^ 5) = (ω : K) ^ 5 := by
    obtain ⟨a, ha⟩ := lmat_col_ne_zero y ιe₁
    rcases a with k | m | k
    · have e := hent (.inl k) ιe₁
      rw [hiE k, show mat (i ^ 5) ιe₁ ιe₁ = (ω : K) ^ 5 from hiE 0] at e
      exact mul_left_cancel₀ ha (e.trans (mul_comm _ _))
    · fin_cases m
      exact absurd (hz 0).2.2.1 ha
    · exact absurd (hEF k 0).2 ha
  have hσ1 : y.1.right = 1 := ringEquiv_eq_one_of_fixes h hf hω hσω
  set A := lmat y with hA
  set B := xBlock A with hB
  have hAcol : ∀ (k : Fin 1 ⊕ Fin 2) (j : Fin 2), A (.inr k) (.inl j) = 0 := by
    rintro (m | k) j
    · fin_cases m
      exact (hz j).2.2.1
    · exact (hEF k j).2
  have hArow : ∀ (k : Fin 1 ⊕ Fin 2) (j : Fin 2), A (.inl j) (.inr k) = 0 := by
    rintro (m | k) j
    · fin_cases m
      exact (hz j).1
    · exact (hEF j k).1
  have hBinv : xBlock ((y.1.left⁻¹ : GL (HypIndex 2 1) K) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K) * B = 1 := by
    have e3 := congrArg xBlock (lmat_mul_inv y).2
    rw [xBlock_mul_of_col hAcol] at e3
    rw [e3]
    ext a b
    simp [xBlock, Matrix.one_apply]
  have hdetB : B.det ≠ 0 := by
    intro h0
    have e := congrArg Matrix.det hBinv
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at e
    exact zero_ne_one e
  obtain ⟨μ, hμ⟩ := (Finite.injective_iff_surjective.1 (frobenius_inj K 2)) B.det
  rw [frobenius_def] at hμ
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hμ
    exact hdetB hμ.symm
  have hdet0 : (μ⁻¹ • B).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, ← hμ, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hμ0)]
  set g₀ : SpecialLinearGroup (Fin 2) K := ⟨μ⁻¹ • B, hdet0⟩ with hg₀
  have hB0 : B = μ • (g₀ : Matrix (Fin 2) (Fin 2) K) := by
    change B = μ • (μ⁻¹ • B)
    rw [smul_smul, mul_inv_cancel₀ hμ0, one_smul]
  refine ⟨UnitaryHigher.leviSU h 1 g₀, ⟨g₀, rfl⟩, fun n hn => ?_⟩
  obtain ⟨C, rfl⟩ := hn
  set n := UnitaryHigher.leviSU h 1 C with hn
  have hnmap : (mat n).map y.1.right = mat n := by
    rw [hσ1]
    ext a b
    rfl
  have hrel := lmat_mul_map y n
  rw [hnmap] at hrel
  have hNcol : ∀ (k : Fin 1 ⊕ Fin 2) (j : Fin 2), mat n (.inr k) (.inl j) = 0 := by
    intro k j
    rw [hn, mat_leviSU]
    rcases k with m | k <;> rfl
  have hEB := congrArg xBlock hrel
  rw [xBlock_mul_of_col hNcol, xBlock_mul_of_col hAcol, hn, xBlock_mat_leviSU] at hEB
  have hn5 : j ^ 5 * n = n * j ^ 5 := N₁sub_comm_I₁sub ⟨C, rfl⟩ (pow_mem hj 5)
  have hc : j ^ 5 * actΓ h y n = actΓ h y n * j ^ 5 := by
    calc j ^ 5 * actΓ h y n = actΓ h y (j ^ 5) * actΓ h y n := by rw [hfixy]
      _ = actΓ h y (j ^ 5 * n) := (act_mul _ _ _).symm
      _ = actΓ h y (n * j ^ 5) := by rw [hn5]
      _ = actΓ h y n * actΓ h y (j ^ 5) := act_mul _ _ _
      _ = actΓ h y n * j ^ 5 := by rw [hfixy]
  have hblkM := mat_eq_blk3_of_comm ht hβ e1 e2 e3 e4 e5 hc
  have hdetM : (xBlock (mat (actΓ h y n))).det = 1 := by
    have e := congrArg Matrix.det hEB
    rw [Matrix.det_mul, Matrix.det_mul, C.2, mul_one] at e
    exact mul_right_cancel₀ hdetB (e.symm.trans (one_mul _).symm)
  obtain ⟨D₁, hD₁⟩ := mem_N₁sub_of_blk3 hblkM hdetM
  have hxD : xBlock (mat (actΓ h y n)) = D₁ := by rw [← hD₁, xBlock_mat_leviSU]
  rw [hxD] at hEB
  rw [← hD₁, hn, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  change B * (C : Matrix (Fin 2) (Fin 2) K) = (D₁ : Matrix (Fin 2) (Fin 2) K) * B at hEB
  have h2 : (g₀ : Matrix (Fin 2) (Fin 2) K) * C = D₁ * g₀ := by
    rw [hB0, Matrix.smul_mul, Matrix.mul_smul] at hEB
    exact smul_right_injective _ hμ0 hEB
  have hBB : (g₀ : Matrix (Fin 2) (Fin 2) K) * ((g₀⁻¹ : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.mul_adjugate, g₀.2, one_smul]
  have h3 : (D₁ : Matrix (Fin 2) (Fin 2) K) =
      ((g₀ * C * g₀⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    calc (D₁ : Matrix (Fin 2) (Fin 2) K) = D₁ * ((g₀ : Matrix (Fin 2) (Fin 2) K) *
          ((g₀⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
            rw [hBB, Matrix.mul_one]
      _ = g₀ * C * ((g₀⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
            rw [← Matrix.mul_assoc, ← h2]
  exact Subtype.ext h3

end Model

end CFSG.LocalAnalysis.EvenBN.U5
