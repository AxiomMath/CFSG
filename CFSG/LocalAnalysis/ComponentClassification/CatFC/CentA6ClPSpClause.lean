module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpBase
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSevenPSpSkew
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSkewNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSevenBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.Burgoyne.Sp (spCent stdSkew skewNs exists_skew_split_normal_form
  exists_skew_nonsplit_normal_form)
open CFSG.SeitzReduction.LinearPilot.SevenList (formJSp stdSkew_mul_formJ)

section Swap

variable {r : ℕ} {K : Type} [Field K]

theorem conj_anticomm {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    {Hm Hi M N W₀ : Matrix n n R} (h1 : Hm * Hi = 1) (h2 : Hi * Hm = 1) (hN : Hi * M * Hm = N)
    (hW : W₀ * N = -(N * W₀)) : (Hm * W₀ * Hi) * M = -(M * (Hm * W₀ * Hi)) := by
  have hMe : M = Hm * N * Hi := by
    rw [← hN]
    calc M = (Hm * Hi) * M * (Hm * Hi) := by rw [h1, Matrix.one_mul, Matrix.mul_one]
      _ = Hm * (Hi * M * Hm) * Hi := by simp only [Matrix.mul_assoc]
  have h3 : ∀ X : Matrix n n R, Hi * (Hm * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [hMe]
  calc Hm * W₀ * Hi * (Hm * N * Hi) = Hm * (W₀ * N) * Hi := by
        simp only [Matrix.mul_assoc, h3]
    _ = -(Hm * N * Hi * (Hm * W₀ * Hi)) := by
        rw [hW]
        simp only [Matrix.mul_assoc, h3, Matrix.mul_neg, Matrix.neg_mul]

theorem negSwap_mul (i : K) (hi : i * i = -1) :
    fromBlocks (i • (1 : Matrix (Fin r) (Fin r) K)) 0 0 ((-i) • (1 : Matrix (Fin r) (Fin r) K)) *
      fromBlocks ((-i) • (1 : Matrix (Fin r) (Fin r) K)) 0 0 (i • (1 : Matrix (Fin r) (Fin r) K)) =
        1 := by
  rw [fromBlocks_multiply, ← fromBlocks_one]
  simp [smul_smul, hi]

theorem negSwap_mul' (i : K) (hi : i * i = -1) :
    fromBlocks ((-i) • (1 : Matrix (Fin r) (Fin r) K)) 0 0 (i • (1 : Matrix (Fin r) (Fin r) K)) *
      fromBlocks (i • (1 : Matrix (Fin r) (Fin r) K)) 0 0 ((-i) • (1 : Matrix (Fin r) (Fin r) K)) =
        1 := by
  rw [fromBlocks_multiply, ← fromBlocks_one]
  simp [smul_smul, hi]

theorem negSwap_sp (i : K) (hi : i * i = -1) :
    (fromBlocks (i • (1 : Matrix (Fin r) (Fin r) K)) 0 0 ((-i) • (1 : Matrix (Fin r) (Fin r) K)))ᵀ *
      fromBlocks 0 1 (-1) 0 *
        fromBlocks (i • (1 : Matrix (Fin r) (Fin r) K)) 0 0
          ((-i) • (1 : Matrix (Fin r) (Fin r) K)) = fromBlocks 0 1 (-1) 0 := by
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp [smul_smul, hi]

theorem negSwap_skewNs (i d : K) (hi : i * i = -1) :
    fromBlocks (i • (1 : Matrix (Fin r) (Fin r) K)) 0 0 ((-i) • (1 : Matrix (Fin r) (Fin r) K)) *
      skewNs r K d = -(skewNs r K d *
        fromBlocks (i • (1 : Matrix (Fin r) (Fin r) K)) 0 0
          ((-i) • (1 : Matrix (Fin r) (Fin r) K))) := by
  rw [skewNs, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_neg]
  simp [smul_smul, hi]
  rw [mul_comm]

variable (r K) in
@[expose] def negSwap (i : K) (hi : i * i = -1) : StatedSp r K :=
  ⟨⟨fromBlocks (i • (1 : Matrix (Fin r) (Fin r) K)) 0 0 ((-i) • (1 : Matrix (Fin r) (Fin r) K)),
    fromBlocks ((-i) • (1 : Matrix (Fin r) (Fin r) K)) 0 0 (i • (1 : Matrix (Fin r) (Fin r) K)),
    negSwap_mul i hi, negSwap_mul' i hi⟩,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mpr
      (negSwap_sp i hi)⟩

theorem exists_swap [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f) (hr : 1 ≤ r) (hi : IsSquare (-1 : K)) {A : gsp r K}
    (hAns : ∀ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c)
    {c : Kˣ}
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (c : K) • 1)
    (hJ : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (-(c : K)) • formJ r K) :
    ∃ w : StatedSp r K,
      ((w : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        -(((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          ((w : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) := by
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hKc
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K ℓ]
    exact hℓ2
  by_cases hsq : ∃ l : K, l ^ 2 = c
  · obtain ⟨l, hl⟩ := hsq
    have hl0 : l ≠ 0 := fun h0 => c.ne_zero (by rw [← hl, h0]; ring)
    obtain ⟨H, hH⟩ := exists_skew_split_normal_form hchar hl0 (by rw [hl]; exact hAA)
      (by rw [hl]; exact hJ)
    refine ⟨H * formJSp r K * H⁻¹, ?_⟩
    refine conj_anticomm (N := l • stdSkew r K) (H : GL (Fin r ⊕ Fin r) K).mul_inv
      (H : GL (Fin r ⊕ Fin r) K).inv_mul hH ?_
    change formJ r K * (l • stdSkew r K) = -((l • stdSkew r K) * formJ r K)
    rw [Matrix.mul_smul, Matrix.smul_mul, stdSkew_mul_formJ, smul_neg, neg_neg]
  · push Not at hsq
    obtain ⟨i, hi⟩ := hi
    obtain ⟨H, hH⟩ := exists_skew_nonsplit_normal_form hℓ hℓ2 hf hKc hr hAns hsq hAA hJ
    refine ⟨H * negSwap r K i hi.symm * H⁻¹, ?_⟩
    refine conj_anticomm (N := skewNs r K (c : K)) (H : GL (Fin r ⊕ Fin r) K).mul_inv
      (H : GL (Fin r ⊕ Fin r) K).inv_mul hH ?_
    exact negSwap_skewNs i (c : K) hi.symm

end Swap

section Torus

variable {r : ℕ} {K : Type} [Field K]

theorem alg_sp {n : Type*} [Fintype n] [DecidableEq n] (J M : Matrix n n K) (a b c : K)
    (hJ : Mᵀ * J * M = (-c) • J) (hMJ : Mᵀ * J = -(J * M)) (h : a ^ 2 - c * b ^ 2 = 1) :
    (a • (1 : Matrix n n K) + b • M)ᵀ * J * (a • (1 : Matrix n n K) + b • M) = J := by
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one]
  have hJ' : Mᵀ * (J * M) = (-c) • J := by rw [← Matrix.mul_assoc]; exact hJ
  have e1 : (a • (1 : Matrix n n K) + b • Mᵀ) * J * (a • (1 : Matrix n n K) + b • M) =
      (a * a) • J + (a * b) • (J * M) + (b * a) • (Mᵀ * J) + (b * b) • (Mᵀ * (J * M)) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_smul, smul_add, Matrix.mul_assoc]
    module
  rw [e1, hJ', hMJ]
  have : (a * a) • J + (a * b) • (J * M) + (b * a) • -(J * M) + (b * b) • ((-c) • J) =
      (a ^ 2 - c * b ^ 2) • J := by
    module
  rw [this, h, one_smul]

theorem alg_mul_conj {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n K) (a b c : K)
    (hMM : M * M = c • 1) (h : a ^ 2 - c * b ^ 2 = 1) :
    (a • (1 : Matrix n n K) + b • M) * (a • (1 : Matrix n n K) - b • M) = 1 := by
  have : (a • (1 : Matrix n n K) + b • M) * (a • (1 : Matrix n n K) - b • M) =
      (a * a) • (1 : Matrix n n K) - (b * b) • (M * M) := by
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_smul, smul_sub]
    module
  rw [this, hMM]
  have : (a * a) • (1 : Matrix n n K) - (b * b) • (c • (1 : Matrix n n K)) =
      (a ^ 2 - c * b ^ 2) • (1 : Matrix n n K) := by module
  rw [this, h, one_smul]

theorem alg_conj_mul {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n K) (a b c : K)
    (hMM : M * M = c • 1) (h : a ^ 2 - c * b ^ 2 = 1) :
    (a • (1 : Matrix n n K) - b • M) * (a • (1 : Matrix n n K) + b • M) = 1 := by
  have : (a • (1 : Matrix n n K) - b • M) * (a • (1 : Matrix n n K) + b • M) =
      (a * a) • (1 : Matrix n n K) - (b * b) • (M * M) := by
    simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_smul, smul_add]
    module
  rw [this, hMM]
  have : (a * a) • (1 : Matrix n n K) - (b * b) • (c • (1 : Matrix n n K)) =
      (a ^ 2 - c * b ^ 2) • (1 : Matrix n n K) := by module
  rw [this, h, one_smul]

theorem alg_sq {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n K) (a b c : K)
    (hMM : M * M = c • 1) :
    (a • (1 : Matrix n n K) - b • M) * (a • (1 : Matrix n n K) - b • M) =
      (a ^ 2 + c * b ^ 2) • (1 : Matrix n n K) - (2 * a * b) • M := by
  have : (a • (1 : Matrix n n K) - b • M) * (a • (1 : Matrix n n K) - b • M) =
      (a * a) • (1 : Matrix n n K) - (a * b) • M - (b * a) • M + (b * b) • (M * M) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_smul, smul_sub]
    module
  rw [this, hMM]
  module

open Polynomial in
theorem exists_good_b [Fintype K] (hK : 6 ≤ Fintype.card K) {c : K}
    (hc : c ≠ 0) : ∃ b : K, b ≠ 0 ∧ c * b ^ 2 ≠ 1 ∧ c * b ^ 2 ≠ -1 := by
  by_contra hne
  push Not at hne
  let p : K[X] := C (c ^ 2) * X ^ 5 - X
  have hp : ∀ b : K, p.eval b = 0 := by
    intro b
    by_cases hb : b = 0
    · simp [p, hb]
    by_cases h1 : c * b ^ 2 = 1
    · have : c ^ 2 * b ^ 5 - b = b * ((c * b ^ 2) ^ 2 - 1) := by ring
      simp only [p, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
      rw [this, h1]
      ring
    · have h2 := hne b hb h1
      have : c ^ 2 * b ^ 5 - b = b * ((c * b ^ 2) ^ 2 - 1) := by ring
      simp only [p, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
      rw [this, h2]
      ring
  have hdeg : p.natDegree < (Finset.univ : Finset K).card := by
    rw [Finset.card_univ]
    refine lt_of_le_of_lt ?_ (by omega : 5 < Fintype.card K)
    refine (natDegree_sub_le _ _).trans ?_
    refine max_le ?_ (by simp)
    exact (natDegree_C_mul_X_pow_le _ _)
  have h0 : p = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p Finset.univ
    (fun b _ => hp b) hdeg
  have h5 : p.coeff 5 = 0 := by rw [h0]; exact coeff_zero 5
  have h5' : p.coeff 5 = c ^ 2 := by
    simp only [p, coeff_sub, coeff_C_mul_X_pow, coeff_X]
    norm_num
  rw [h5'] at h5
  exact hc (pow_eq_zero_iff (by norm_num) |>.mp h5)

end Torus

section TorusElement

variable {r : ℕ} {K : Type} [Field K]

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.Burgoyne.Sp (mem_spCent)

theorem exists_torus [Finite K] [NeZero r] (h2 : (2 : K) ≠ 0) (h6 : 6 ≤ Nat.card K)
    {A : gsp r K}
    (hAns : ∀ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c)
    {c : Kˣ}
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (c : K) • 1)
    (hJ : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (-(c : K)) • formJ r K)
    {w : StatedSp r K}
    (hw : ((w : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      -(((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((w : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))) :
    ∃ t : spCent r K A, (∀ y : spCent r K A, y * t = t * y) ∧
      w * (t : StatedSp r K) * w⁻¹ = (t : StatedSp r K)⁻¹ ∧
      proj r K ((t : StatedSp r K)⁻¹ * (t : StatedSp r K)⁻¹) ≠ 1 := by
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  set W := ((w : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hW
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hMns : ∀ k : K, M ≠ k • 1 := by
    intro k hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hk
      rw [hk, Matrix.zero_mul] at hAA
      have h3 := congrFun (congrFun hAA (Sum.inl ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩))
        (Sum.inl ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩)
      simp only [Matrix.zero_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
        mul_one] at h3
      exact hc0 h3.symm
    refine hAns (Units.mk0 k hk0) (Units.ext ?_)
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
    exact hk
  have hMJ : Mᵀ * formJ r K = -(formJ r K * M) := by
    have e1 : Mᵀ * formJ r K * (M * M) = (Mᵀ * formJ r K * M) * M := by
      rw [← Matrix.mul_assoc (Mᵀ * formJ r K) M M]
    rw [hAA, hJ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at e1
    have e2 : (c : K) • (Mᵀ * formJ r K) = (c : K) • (-(formJ r K * M)) := by
      rw [e1, smul_neg, neg_smul]
    exact smul_right_injective _ hc0 e2
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨b, hb0, hb1, hb2⟩ := exists_good_b (K := K) (by rwa [← Nat.card_eq_fintype_card]) hc0
  have hn : (1 - (c : K) * b ^ 2) ≠ 0 := fun h => hb1 (by linear_combination -h)
  have hn' : (1 + (c : K) * b ^ 2) ≠ 0 := fun h => hb2 (by linear_combination h)
  set a' : K := (1 + (c : K) * b ^ 2) / (1 - (c : K) * b ^ 2) with ha'def
  set b' : K := 2 * b / (1 - (c : K) * b ^ 2) with hb'def
  have ha' : a' ^ 2 - (c : K) * b' ^ 2 = 1 := by
    rw [ha'def, hb'def]
    field_simp
    ring
  have ha'0 : a' ≠ 0 := div_ne_zero hn' hn
  have hb'0 : b' ≠ 0 := div_ne_zero (mul_ne_zero h2 hb0) hn
  set tm : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := a' • 1 + b' • M with htm
  set ti : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := a' • 1 - b' • M with hti
  have htti : tm * ti = 1 := alg_mul_conj M a' b' (c : K) hAA ha'
  have hitt : ti * tm = 1 := alg_conj_mul M a' b' (c : K) hAA ha'
  let tG : GL (Fin r ⊕ Fin r) K := ⟨tm, ti, htti, hitt⟩
  have htS : tG ∈ StatedSp r K := mem_statedSp_iff.mpr (alg_sp (formJ r K) M a' b' (c : K) hJ hMJ ha')
  let tS : StatedSp r K := ⟨tG, htS⟩
  have htcomm : ∀ Y : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K, M * Y = Y * M → tm * Y = Y * tm := by
    intro Y hY
    simp only [htm, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, hY]
  have htC : tS ∈ spCent r K A := mem_spCent.mpr (htcomm M rfl).symm
  refine ⟨⟨tS, htC⟩, ?_, ?_, ?_⟩
  · intro y
    apply Subtype.ext
    apply statedSp_ext
    exact (htcomm _ (mem_spCent.mp y.2)).symm
  · apply statedSp_ext
    set Wi := (((w⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hWi
    have hWWi : W * Wi = 1 := by
      rw [hWi, hW, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
        Units.val_one]
    change W * tm * Wi = ti
    calc W * tm * Wi = a' • (W * Wi) + b' • (W * M * Wi) := by
          simp only [htm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_one]
      _ = ti := by
          rw [hw, hWWi, Matrix.neg_mul, Matrix.mul_assoc, hWWi, Matrix.mul_one, smul_neg,
            ← sub_eq_add_neg]
  · intro h1
    have h2' : tS⁻¹ * tS⁻¹ ∈ spScalars r K := by
      rw [← ker_proj]
      exact h1
    have h3 := h2'
    rw [spScalars, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h3
    obtain ⟨c₀, hc₀⟩ := h3
    have h4 : ti * ti = (c₀ : K) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
      have := congrArg (fun g : GL (Fin r ⊕ Fin r) K =>
        (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) hc₀
      simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at this
      rw [Matrix.smul_one_eq_diagonal]
      exact this.symm
    have h5 : ((a' ^ 2 + (c : K) * b' ^ 2) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) -
        (2 * a' * b') • M) = (c₀ : K) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
      rw [← alg_sq M a' b' (c : K) hAA]
      exact h4
    have hne : 2 * a' * b' ≠ 0 := mul_ne_zero (mul_ne_zero h2 ha'0) hb'0
    have h6 : (2 * a' * b') • M =
        ((a' ^ 2 + (c : K) * b' ^ 2) - (c₀ : K)) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
      rw [sub_smul, ← h5, sub_sub_cancel]
    exact hMns (((2 * a' * b')⁻¹) * ((a' ^ 2 + (c : K) * b' ^ 2) - (c₀ : K))) (by
      calc M = (2 * a' * b')⁻¹ • ((2 * a' * b') • M) := by
            rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
        _ = _ := by rw [h6, smul_smul])

end TorusElement

section Clause

variable {r : ℕ} {K : Type} [Field K]

theorem proj_conjSp_of_anticomm {A : gsp r K} {w : StatedSp r K}
    (hw : ((w : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      -(((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((w : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))) :
    proj r K (conjSp r K A w) = proj r K w := by
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  set P := ((w : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hP
  have hkey : M * P = -(P * M) := by rw [hw, neg_neg]
  set Pi := (((w⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hPi
  set Mi := (((A : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hMi
  have h1 : Pi * P = 1 := by
    rw [hPi, hP, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
      Units.val_one]
  have h2 : M * Mi = 1 := (A : GL (Fin r ⊕ Fin r) K).mul_inv
  have hz : ((w⁻¹ * conjSp r K A w : StatedSp r K) : GL (Fin r ⊕ Fin r) K) =
      GeneralLinearGroup.scalar (Fin r ⊕ Fin r) (-1) := by
    apply Units.ext
    have hlhs : (((w⁻¹ * conjSp r K A w : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = Pi * (M * P * Mi) := rfl
    rw [hlhs, hkey, GeneralLinearGroup.coe_scalar]
    calc Pi * (-(P * M) * Mi) = -((Pi * P) * (M * Mi)) := by
          simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = Matrix.scalar (Fin r ⊕ Fin r) ((-1 : Kˣ) : K) := by
          rw [h1, h2, Matrix.one_mul, Units.val_neg, Units.val_one, Matrix.scalar_apply,
            ← Matrix.diagonal_one, Matrix.diagonal_neg]
  have hmem : w⁻¹ * conjSp r K A w ∈ spScalars r K := by
    rw [spScalars, Subgroup.mem_subgroupOf, StatedScalars]
    exact ⟨-1, hz.symm⟩
  rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hmem
  exact hmem.symm

theorem clause_of_swap [Finite K] {A : gsp r K}
    {D : Subgroup ↥(fixedSubgroup (conjAut r K A))}
    (hD : Nonempty (↥D ≃* alternatingGroup (Fin 6)))
    (hH : ∃ H : Subgroup (spCent r K A), H.map (spCentFix A) = D)
    (w : StatedSp r K) (hw : proj r K (conjSp r K A w) = proj r K w)
    (t : spCent r K A) (htc : ∀ y : spCent r K A, y * t = t * y)
    (hwt : w * (t : StatedSp r K) * w⁻¹ = (t : StatedSp r K)⁻¹)
    (hnot : proj r K ((t : StatedSp r K)⁻¹ * (t : StatedSp r K)⁻¹) ≠ 1) :
    ∃ a b : ↥(fixedSubgroup (conjAut r K A)), a * b * a⁻¹ * b⁻¹ ∉ D := by
  obtain ⟨H, hHD⟩ := hH
  let a : ↥(fixedSubgroup (conjAut r K A)) := ⟨proj r K w, by
    change conjAut r K A (proj r K w) = proj r K w
    rw [conjAut_proj]
    exact hw⟩
  let b : ↥(fixedSubgroup (conjAut r K A)) := spCentFix A t
  refine ⟨a, b, fun hmem => ?_⟩
  have hcomm : a * b * a⁻¹ * b⁻¹ = spCentFix A (t⁻¹ * t⁻¹) := by
    apply Subtype.ext
    change proj r K w * proj r K (t : StatedSp r K) * (proj r K w)⁻¹ *
      (proj r K (t : StatedSp r K))⁻¹ = proj r K (((t⁻¹ * t⁻¹ : spCent r K A)) : StatedSp r K)
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    have : w * (t : StatedSp r K) * w⁻¹ * (t : StatedSp r K)⁻¹ =
        (t : StatedSp r K)⁻¹ * (t : StatedSp r K)⁻¹ := by rw [hwt]
    rw [this]
    rfl
  rw [hcomm] at hmem
  have hz1 : spCentFix A (t⁻¹ * t⁻¹) = 1 := by
    obtain ⟨e⟩ := hD
    set z : ↥D := ⟨_, hmem⟩ with hzdef
    have hcent : z ∈ center ↥D := by
      rw [Subgroup.mem_center_iff]
      intro d
      have hd : d.1 ∈ H.map (spCentFix A) := hHD ▸ d.2
      obtain ⟨y, -, hy⟩ := hd
      apply Subtype.ext
      change d.1 * spCentFix A (t⁻¹ * t⁻¹) = spCentFix A (t⁻¹ * t⁻¹) * d.1
      rw [← hy, ← map_mul, ← map_mul]
      congr 1
      have hc : Commute y t := htc y
      have h2 : Commute y (t⁻¹ * t⁻¹) := hc.inv_right.mul_right hc.inv_right
      exact h2.eq
    have hez : e z ∈ center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨d, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subgroup.mem_center_iff.mp hcent d
    rw [a6sq_center, Subgroup.mem_bot] at hez
    have hz : z = 1 := e.injective (by rw [hez, map_one])
    exact congrArg Subtype.val hz
  have := (spCentFix_eq_one_iff A (t⁻¹ * t⁻¹)).1 hz1
  exact hnot this

theorem clause_psp [NeZero r] [Finite K] {f : ℕ} (hf : 1 ≤ f) (hKc : Nat.card K = 3 ^ f)
    (hi : IsSquare (-1 : K)) (h6 : 6 ≤ Nat.card K) {A : gsp r K}
    (hA : orderOf (conjAut r K A) = 2) {c : Kˣ}
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (c : K) • 1)
    (hJ : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (-(c : K)) • formJ r K)
    (hP : Perfect360 (spCent r K A))
    {D : Subgroup ↥(fixedSubgroup (conjAut r K A))} (h : A6Hyp (conjAut r K A) D) :
    ∃ a b : ↥(fixedSubgroup (conjAut r K A)), a * b * a⁻¹ * b⁻¹ ∉ D := by
  have hr : 1 ≤ r := Nat.pos_of_ne_zero (NeZero.ne r)
  have : CharP K 3 := finite_field_prime_power_characteristic Nat.prime_three hf hKc
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K 3]
    norm_num
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hchar
  have hA1 : conjAut r K A ≠ 1 := fun h => by
    rw [h, orderOf_one] at hA
    exact absurd hA (by norm_num)
  have hAns : ∀ c : Kˣ,
      (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c :=
    fun c hc => hA1 ((Burgoyne.Sp.conjAut_eq_one_iff hr A).2 ⟨c, hc⟩)
  obtain ⟨w, hw⟩ := exists_swap Nat.prime_three (by norm_num) hf hKc hr hi hAns hAA hJ
  obtain ⟨t, htc, hwt, hnot⟩ := exists_torus h2 h6 hAns hAA hJ hw
  exact clause_of_swap h.2.1 (h.exists_map_eq_of_perfect360 hr hP) w
    (proj_conjSp_of_anticomm hw) t htc hwt hnot

end Clause

end CFSG.ComponentClassification.CatFC
