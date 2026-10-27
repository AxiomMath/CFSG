module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneORes
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthCore

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup
open CFSG.ComponentClassification.Burgoyne.PSL (signMat compInd commute_signMat_iff
  commute_compInd_iff reflGL rotGL rotMat planeP planeN commutatorElement_reflGL_rotGL
  eq_one_of_fix_circle)
open scoped commutatorElement

variable {K : Type} [Field K]

theorem kronI_diagonal (n : ℕ) (v : Fin n → K) :
    kronI K n (diagonal v) = diagonal fun p => v ((pairEquiv n).symm p).1 := by
  ext p q
  obtain ⟨⟨i, j⟩, rfl⟩ := (pairEquiv n).surjective p
  obtain ⟨⟨k, l⟩, rfl⟩ := (pairEquiv n).surjective q
  rw [kronI_apply, diagonal_apply, diagonal_apply, Equiv.symm_apply_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases hik : i = k
  · subst hik
    by_cases hjl : j = l <;> simp [hjl]
  · simp [hik]

@[expose] def pairSet {n : ℕ} (S : Finset (Fin n)) : Finset (Fin (2 * n)) :=
  Finset.univ.filter fun p => ((pairEquiv n).symm p).1 ∈ S

theorem mem_pairSet {n : ℕ} (S : Finset (Fin n)) (x : Fin n) (a : Fin 2) :
    pairEquiv n (x, a) ∈ pairSet S ↔ x ∈ S := by
  simp [pairSet]

theorem kronI_signMat (n : ℕ) (S : Finset (Fin n)) :
    kronI K n (signMat K S) = signMat K (pairSet S) := by
  rw [signMat, kronI_diagonal, signMat]
  congr 1
  ext p
  obtain ⟨⟨i, j⟩, rfl⟩ := (pairEquiv n).surjective p
  simp only [Equiv.symm_apply_apply, mem_pairSet]

theorem trace_rotMat {n : ℕ} {i j : Fin n} (hij : i ≠ j) (a b : K) :
    (rotMat i j a b).trace = n + 2 * (a - 1) := by
  rw [rotMat, trace_add, trace_add, trace_one, trace_smul, trace_smul, planeP, planeN,
    trace_add, trace_sub, trace_single_eq_same, trace_single_eq_same,
    trace_single_eq_of_ne _ _ _ hij, trace_single_eq_of_ne _ _ _ (Ne.symm hij), Fintype.card_fin]
  simp only [smul_eq_mul]
  ring

theorem trace_map_ringEquiv {m : Type*} [Fintype m] (τ : K ≃+* K) (M : Matrix m m K) :
    (M.map τ).trace = τ M.trace := by
  simp only [Matrix.trace, diag_apply, map_apply, map_sum]

theorem trace_conj {m : Type*} [Fintype m] [DecidableEq m] (D : GL m K) (M : Matrix m m K) :
    ((D : Matrix m m K) * M * ((D⁻¹ : GL m K) : Matrix m m K)).trace = M.trace := by
  rw [trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul]

variable [Finite K]

theorem tau_eq_one_of_sq (hK : ringChar K ≠ 2) {τ : K ≃+* K} {m : ℕ} (hm : Odd m)
    (hτm : τ ^ m = 1) (h : ∀ a b : K, a ^ 2 + b ^ 2 = 1 → τ (a ^ 2 - b ^ 2) = a ^ 2 - b ^ 2) :
    τ = 1 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  refine eq_one_of_fix_circle hK fun a b hab => ?_
  have e' := h a b hab
  have hb : b ^ 2 = 1 - a ^ 2 := by linear_combination hab
  rw [hb] at e'
  have hτa2 : τ (a ^ 2) = a ^ 2 := by
    have e2 : τ (2 * a ^ 2 - 1) = 2 * a ^ 2 - 1 := by
      have h3 : (2 * a ^ 2 - 1 : K) = a ^ 2 - (1 - a ^ 2) := by ring
      rw [h3]
      exact e'
    rw [map_sub, map_mul, map_one, map_ofNat] at e2
    have : (2 : K) * (τ (a ^ 2) - a ^ 2) = 0 := by linear_combination e2
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h2)
  rw [map_pow] at hτa2
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hτa2 with h' | h'
  · exact h'
  · have hpow : ∀ k : ℕ, (τ ^ k) a = (-1) ^ k * a := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ]
        change (τ ^ k) (τ a) = _
        rw [h', map_neg, ih, pow_succ]
        ring
    have := hpow m
    rw [hτm, hm.neg_one_pow] at this
    change a = -1 * a at this
    have ha0 : a = 0 := by
      have : (2 : K) * a = 0 := by linear_combination this
      exact (mul_eq_zero.1 this).resolve_left h2
    rw [h', ha0, neg_zero]

theorem tau_eq_one_of_kron (hK : ringChar K ≠ 2) {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {D : GL (Fin (2 * n)) K} {τ : K ≃+* K} {m : ℕ} (hm : Odd m) (hτm : τ ^ m = 1)
    (hfix : ∀ (a b : K) (hab : a ^ 2 + b ^ 2 = 1),
      (D : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
          (kronI K n ((⁅reflGL (K := K) i, rotGL i j hij hab⁆ : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K)).map τ *
          ((D⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
        kronI K n ((⁅reflGL (K := K) i, rotGL i j hij hab⁆ : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K)) :
    τ = 1 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  refine tau_eq_one_of_sq hK hm hτm fun a b hab => ?_
  have e := congrArg Matrix.trace (hfix a b hab)
  rw [trace_conj, trace_map_ringEquiv, trace_kronI, commutatorElement_reflGL_rotGL,
    trace_rotMat hij] at e
  rw [map_mul, map_add, map_mul, map_sub, map_natCast, map_ofNat, map_one] at e
  have : (4 : K) * (τ (a ^ 2 - b ^ 2) - (a ^ 2 - b ^ 2)) = 0 := by linear_combination e
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h4)

omit [Finite K] in
theorem kron_iso_of_sign (h2 : (2 : K) ≠ 0) {n : ℕ} {I₀ : Finset (Fin n)} (hI₀ : 3 ≤ I₀.card)
    {D : Matrix (Fin (2 * n)) (Fin (2 * n)) K}
    (hS : ∀ i ∈ I₀, ∀ j ∈ I₀, i ≠ j →
      D * kronI K n (signMat K {i, j}) = kronI K n (signMat K {i, j}) * D)
    {x : Fin n} (hx : x ∈ I₀) {y : Fin n} (hyx : y ≠ x) (a b : Fin 2) :
    D (pairEquiv n (x, a)) (pairEquiv n (y, b)) = 0 ∧
      D (pairEquiv n (y, b)) (pairEquiv n (x, a)) = 0 := by
  obtain ⟨z, hz, hzx, hzy⟩ : ∃ z ∈ I₀, z ≠ x ∧ z ≠ y := by
    have hc : 0 < ((I₀.erase x).erase y).card := by
      have h1 := Finset.pred_card_le_card_erase (s := I₀) (a := x)
      have h2 := Finset.pred_card_le_card_erase (s := I₀.erase x) (a := y)
      omega
    obtain ⟨z, hz⟩ := Finset.card_pos.1 hc
    simp only [Finset.mem_erase] at hz
    exact ⟨z, hz.2.2, hz.2.1, hz.1⟩
  have hc := hS x hx z hz (Ne.symm hzx)
  rw [kronI_signMat] at hc
  have hc' := (commute_compInd_iff _ D).1 ((commute_signMat_iff h2 _ D).1 hc.symm)
  have hxJ : pairEquiv n (x, a) ∈ pairSet ({x, z} : Finset (Fin n)) := by
    rw [mem_pairSet]
    simp
  have hyJ : pairEquiv n (y, b) ∉ pairSet ({x, z} : Finset (Fin n)) := by
    rw [mem_pairSet]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hyx, Ne.symm hzy⟩
  exact ⟨hc' _ _ ⟨fun _ => hyJ, fun _ => hxJ⟩,
    hc' _ _ ⟨fun h => absurd h hyJ, fun h => absurd hxJ h⟩⟩

omit [Finite K] in
theorem permMatrix_apply' {n : ℕ} (σ : Equiv.Perm (Fin n)) (x y : Fin n) :
    σ.permMatrix K x y = if σ x = y then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

omit [Finite K] in
theorem kron_block_eq_of_perm {n : ℕ} {D : Matrix (Fin (2 * n)) (Fin (2 * n)) K}
    (σ : Equiv.Perm (Fin n))
    (hσ : D * kronI K n (σ.permMatrix K) = kronI K n (σ.permMatrix K) * D)
    (x : Fin n) (a b : Fin 2) :
    D (pairEquiv n (x, a)) (pairEquiv n (x, b)) =
      D (pairEquiv n (σ x, a)) (pairEquiv n (σ x, b)) := by
  have e := congrFun (congrFun hσ (pairEquiv n (x, a))) (pairEquiv n (σ x, b))
  rw [Matrix.mul_apply, Matrix.mul_apply, ← (pairEquiv n).sum_comp, ← (pairEquiv n).sum_comp,
    Fintype.sum_prod_type, Fintype.sum_prod_type] at e
  simp only [kronI_apply, permMatrix_apply'] at e
  rw [Finset.sum_eq_single x, Finset.sum_eq_single (σ x)] at e
  · simpa [Fin.sum_univ_two, eq_comm] using e
  · intro z _ hz
    simp [Ne.symm hz]
  · simp
  · intro z _ hz
    simp [σ.injective.ne hz]
  · simp

theorem commutator_swap_inv_apply {n : ℕ} {i j k : Fin n} (hjk : j ≠ k) (hik : i ≠ k) :
    (⁅Equiv.swap i j, Equiv.swap j k⁆)⁻¹ i = j := by
  rw [Equiv.Perm.inv_eq_iff_eq, commutatorElement_def]
  simp only [Equiv.Perm.mul_apply, Equiv.swap_inv, Equiv.swap_apply_left]
  rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk), Equiv.swap_apply_right,
    Equiv.swap_apply_right]

omit [Finite K] in
theorem eq_blkDiag_of_kron (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 3 ≤ n)
    {D : Matrix (Fin (2 * n)) (Fin (2 * n)) K}
    (hS : ∀ i j : Fin n, i ≠ j →
      D * kronI K n (signMat K {i, j}) = kronI K n (signMat K {i, j}) * D)
    (hP : ∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
      D * kronI K n ((⁅Equiv.swap i j, Equiv.swap j k⁆)⁻¹.permMatrix K) =
        kronI K n ((⁅Equiv.swap i j, Equiv.swap j k⁆)⁻¹.permMatrix K) * D) :
    D = blkDiag n (Matrix.of fun a b =>
      D (pairEquiv n (⟨0, by omega⟩, a)) (pairEquiv n (⟨0, by omega⟩, b))) := by
  have hI : 3 ≤ (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact hn
  have hiso : ∀ x y : Fin n, x ≠ y → ∀ a b : Fin 2,
      D (pairEquiv n (x, a)) (pairEquiv n (y, b)) = 0 := fun x y hxy a b =>
    (kron_iso_of_sign h2 hI (fun i _ j _ hij => hS i j hij) (Finset.mem_univ x)
      (Ne.symm hxy) a b).1
  have hblk : ∀ x y : Fin n, ∀ a b : Fin 2, D (pairEquiv n (x, a)) (pairEquiv n (x, b)) =
      D (pairEquiv n (y, a)) (pairEquiv n (y, b)) := by
    intro x y a b
    by_cases hxy : x = y
    · rw [hxy]
    obtain ⟨k, hkx, hky⟩ : ∃ k : Fin n, k ≠ x ∧ k ≠ y := by
      have hc : 0 < ((Finset.univ.erase x).erase y).card := by
        have h1 := Finset.pred_card_le_card_erase (s := (Finset.univ : Finset (Fin n))) (a := x)
        have h2 := Finset.pred_card_le_card_erase (s := Finset.univ.erase x) (a := y)
        omega
      obtain ⟨z, hz⟩ := Finset.card_pos.1 hc
      simp only [Finset.mem_erase] at hz
      exact ⟨z, hz.2.1, hz.1⟩
    have e := kron_block_eq_of_perm _ (hP x y k hxy (Ne.symm hky) (Ne.symm hkx)) x a b
    rwa [commutator_swap_inv_apply (Ne.symm hky) (Ne.symm hkx)] at e
  ext p q
  obtain ⟨⟨i, a⟩, rfl⟩ := (pairEquiv n).surjective p
  obtain ⟨⟨k, b⟩, rfl⟩ := (pairEquiv n).surjective q
  rw [blkDiag_apply]
  split_ifs with hik
  · rw [hik, hblk k ⟨0, by omega⟩ a b, of_apply]
  · exact hiso i k hik a b

end CFSG.ComponentClassification.Burgoyne.O
