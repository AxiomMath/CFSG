module

public import CFSG.ClassicalInvolution.Models.LinearPairs.RootSL2
public import CFSG.LieType.Universal.SpecialLinear

public section

namespace CFSG.ClassicalInvolution.Models

open Matrix CFSG.ClassicalInvolution.WeakCT Module CFSG.LieType.Universal.SpecialLinear
open CFSG.ClassicalInvolution.Phan (blockMat blockSel blockMat_apply blockIdx blockSel_mulVec
  blockSel_transpose_mul_self blockMat_apply_blockIdx)
open scoped MatrixGroups

section Eigen

variable {K : Type} [Field K] {n : ℕ}

theorem eigSpace_conj_aux {P Q : Matrix (Fin n) (Fin n) K} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (N : Matrix (Fin n) (Fin n) K) (c : K) :
    eigSpace (P * N * Q) c = (eigSpace N c).map (Matrix.toLin' P) := by
  ext v
  rw [Submodule.mem_map]
  constructor
  · intro hv
    rw [mem_eigSpace] at hv
    refine ⟨Q *ᵥ v, ?_, ?_⟩
    · rw [mem_eigSpace]
      have h1 := congrArg (fun w => Q *ᵥ w) hv
      simp only [mulVec_mulVec, Matrix.mulVec_smul] at h1
      have e : Q * (P * N * Q) = N * Q := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
      rw [e] at h1
      rw [mulVec_mulVec]
      exact h1
    · simp [Matrix.toLin'_apply, mulVec_mulVec, hPQ]
  · rintro ⟨u, hu, rfl⟩
    rw [mem_eigSpace] at hu ⊢
    have e : (P * N * Q) * P = P * N := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hQP, Matrix.mul_one]
    rw [Matrix.toLin'_apply, mulVec_mulVec, e, ← mulVec_mulVec, hu, Matrix.mulVec_smul]

theorem eigSpace_conj (g : SL(n, K)) (N : Matrix (Fin n) (Fin n) K) (c : K) :
    eigSpace ((g : Matrix (Fin n) (Fin n) K) * N * ((g⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K))
        c = (eigSpace N c).map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)) :=
  eigSpace_conj_aux (coe_mul_coe_inv g) (coe_inv_mul_coe g) N c

theorem finrank_map_toLin' {P Q : Matrix (Fin n) (Fin n) K} (hQP : Q * P = 1)
    (U : Submodule K (Fin n → K)) : finrank K (U.map (Matrix.toLin' P)) = finrank K U := by
  have hinj : Function.Injective (Matrix.toLin' P) := by
    intro u u' h
    have := congrArg (fun w => Q *ᵥ w) h
    simpa [Matrix.toLin'_apply, mulVec_mulVec, hQP] using this
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj U)).symm

theorem eigSpace_negBlock_neg_one (h2 : (2 : K) ≠ 0) {j : ℕ} (hj : j + 2 ≤ n) :
    eigSpace (negBlock K n j) (-1) = LinearMap.range (Matrix.mulVecLin (blockSel K n 2 j)) := by
  ext v
  rw [mem_eigSpace, LinearMap.mem_range]
  constructor
  · intro hv
    have hout : ∀ a : Fin n, ¬ (j ≤ a.val ∧ a.val < j + 2) → v a = 0 := by
      intro a ha
      have := congr_fun hv a
      rw [negBlock_eq_diagonal, Matrix.mulVec_diagonal] at this
      simp only [ha, ite_false, Pi.smul_apply, smul_eq_mul] at this
      have h' : (2 : K) * v a = 0 := by linear_combination this
      exact (mul_eq_zero.mp h').resolve_left h2
    refine ⟨fun x => v (blockIdx j hj x), ?_⟩
    ext a
    rw [Matrix.mulVecLin_apply, blockSel_mulVec]
    split_ifs with ha
    · congr 1
      apply Fin.ext
      simp only [blockIdx]
      omega
    · exact (hout a ha).symm
  · rintro ⟨w, rfl⟩
    ext a
    rw [negBlock_eq_diagonal, Matrix.mulVec_diagonal]
    simp only [Matrix.mulVecLin_apply, blockSel_mulVec, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp

theorem finrank_eigSpace_negBlock (h2 : (2 : K) ≠ 0) {j : ℕ} (hj : j + 2 ≤ n) :
    finrank K (eigSpace (negBlock K n j) (-1)) = 2 := by
  rw [eigSpace_negBlock_neg_one h2 hj, LinearMap.finrank_range_of_inj, Module.finrank_fin_fun]
  intro w w' h
  have := congrArg (fun u => (blockSel K n 2 j)ᵀ *ᵥ u) h
  simpa [mulVec_mulVec, blockSel_transpose_mul_self hj] using this

theorem finrank_eigSpace_conj_neg_one (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) (g : SL(n, K)) :
    finrank K (eigSpace (((g * rootInv K hn * g⁻¹ : SL(n, K))) : Matrix (Fin n) (Fin n) K)
      (-1)) = 2 := by
  have e : (((g * rootInv K hn * g⁻¹ : SL(n, K))) : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * negBlock K n 0 *
        ((g⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_rootInv]
  rw [e, eigSpace_conj, finrank_map_toLin' (coe_inv_mul_coe g),
    finrank_eigSpace_negBlock h2 (by omega)]

end Eigen

section Commuting

variable {K : Type} [Field K] {n : ℕ}

theorem sub_one_mul_sub_one_eq_zero {R : Type*} [Ring R] [Algebra K R] (h2 : (2 : K) ≠ 0)
    {X Y A B : R} (hX : X * (1 + A) = 1 + A) (hY : (1 + B) * Y = 1 + B)
    (hQ : (1 - A) * (1 - B) = 0) : (X - 1) * (Y - 1) = 0 := by
  have h4 := four_ne_zero_of_two_ne_zero h2
  have e1 : (X - 1) * (1 - A) = (2 : K) • (X - 1) := by
    have h : (X - 1) * (1 + A) = 0 := by rw [sub_mul, hX, one_mul, sub_self]
    have h' : (X - 1) * A = -(X - 1) := by
      rw [mul_add, mul_one] at h
      exact eq_neg_of_add_eq_zero_right h
    rw [mul_sub, mul_one, h', sub_neg_eq_add, two_smul]
  have e2 : (1 - B) * (Y - 1) = (2 : K) • (Y - 1) := by
    have h : (1 + B) * (Y - 1) = 0 := by rw [mul_sub, hY, mul_one, sub_self]
    have h' : B * (Y - 1) = -(Y - 1) := by
      rw [add_mul, one_mul] at h
      exact eq_neg_of_add_eq_zero_right h
    rw [sub_mul, one_mul, h', sub_neg_eq_add, two_smul]
  have h : (4 : K) • ((X - 1) * (Y - 1)) = 0 := by
    calc (4 : K) • ((X - 1) * (Y - 1)) = ((2 : K) • (X - 1)) * ((2 : K) • (Y - 1)) := by
          rw [smul_mul_smul_comm]
          norm_num
      _ = ((X - 1) * (1 - A)) * ((1 - B) * (Y - 1)) := by rw [e1, e2]
      _ = (X - 1) * ((1 - A) * (1 - B)) * (Y - 1) := by simp only [mul_assoc]
      _ = 0 := by rw [hQ, mul_zero, zero_mul]
  exact (smul_eq_zero.mp h).resolve_left h4

theorem eigSpace_neg_one_le_one {I₁ I₂ : Matrix (Fin n) (Fin n) K}
    (h₂ : I₂ * I₂ = 1) (hc : I₁ * I₂ = I₂ * I₁)
    (hV : eigSpace I₁ (-1) ⊓ eigSpace I₂ (-1) = ⊥) : eigSpace I₁ (-1) ≤ eigSpace I₂ 1 := by
  intro v hv
  rw [mem_eigSpace_neg_one] at hv
  rw [mem_eigSpace_one]
  have h12 : I₁ *ᵥ (I₂ *ᵥ v) = -(I₂ *ᵥ v) := by
    rw [mulVec_mulVec, hc, ← mulVec_mulVec, hv, Matrix.mulVec_neg]
  have hw : v - I₂ *ᵥ v ∈ eigSpace I₁ (-1) ⊓ eigSpace I₂ (-1) := by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_eigSpace_neg_one, Matrix.mulVec_sub, hv, h12]
      abel
    · rw [mem_eigSpace_neg_one, Matrix.mulVec_sub, mulVec_mulVec, h₂, Matrix.one_mulVec]
      abel
  rw [hV, Submodule.mem_bot] at hw
  exact (sub_eq_zero.mp hw).symm

theorem one_sub_mul_one_sub_eq_zero {I₁ I₂ : Matrix (Fin n) (Fin n) K} (h₂ : I₂ * I₂ = 1)
    (hle : eigSpace I₂ (-1) ≤ eigSpace I₁ 1) : (1 - I₁) * (1 - I₂) = 0 := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [← mulVec_mulVec, Matrix.zero_mulVec]
  have hu' : (1 - I₂) *ᵥ v = v - I₂ *ᵥ v := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  have hu : v - I₂ *ᵥ v ∈ eigSpace I₂ (-1) := by
    rw [mem_eigSpace_neg_one, Matrix.mulVec_sub, mulVec_mulVec, h₂, Matrix.one_mulVec]
    abel
  have := mem_eigSpace_one.mp (hle hu)
  rw [hu', Matrix.sub_mulVec, Matrix.one_mulVec, this, sub_self]

theorem mul_comm_of_inf_eq_bot (h2 : (2 : K) ≠ 0) {I₁ I₂ : Matrix (Fin n) (Fin n) K}
    (h₁ : I₁ * I₁ = 1) (h₂ : I₂ * I₂ = 1) (hc : I₁ * I₂ = I₂ * I₁)
    (hV : eigSpace I₁ (-1) ⊓ eigSpace I₂ (-1) = ⊥) {x y : SL(n, K)}
    (hx : x ∈ longRootGroup I₁) (hy : y ∈ longRootGroup I₂) : x * y = y * x := by
  have hle12 := eigSpace_neg_one_le_one h₂ hc hV
  have hle21 := eigSpace_neg_one_le_one h₁ hc.symm (by rwa [inf_comm])
  have Q12 := one_sub_mul_one_sub_eq_zero h₂ hle21
  have Q21 := one_sub_mul_one_sub_eq_zero h₁ hle12
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hx3 : (1 + I₁) * (x : Matrix (Fin n) (Fin n) K) = 1 + I₁ := by
    calc (1 + I₁) * (x : Matrix (Fin n) (Fin n) K) = x + I₁ * x := by rw [add_mul, one_mul]
      _ = x + x * I₁ := by rw [hx1]
      _ = (x : Matrix (Fin n) (Fin n) K) * (1 + I₁) := by rw [mul_add, mul_one]
      _ = 1 + I₁ := hx2
  have hy3 : (1 + I₂) * (y : Matrix (Fin n) (Fin n) K) = 1 + I₂ := by
    calc (1 + I₂) * (y : Matrix (Fin n) (Fin n) K) = y + I₂ * y := by rw [add_mul, one_mul]
      _ = y + y * I₂ := by rw [hy1]
      _ = (y : Matrix (Fin n) (Fin n) K) * (1 + I₂) := by rw [mul_add, mul_one]
      _ = 1 + I₂ := hy2
  have e1 := sub_one_mul_sub_one_eq_zero h2 hx2 hy3 Q12
  have e2 := sub_one_mul_sub_one_eq_zero h2 hy2 hx3 Q21
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  calc (x : Matrix (Fin n) (Fin n) K) * y
      = ((x : Matrix (Fin n) (Fin n) K) - 1) * ((y : Matrix (Fin n) (Fin n) K) - 1) +
          x + y - 1 := by noncomm_ring
    _ = ((y : Matrix (Fin n) (Fin n) K) - 1) * ((x : Matrix (Fin n) (Fin n) K) - 1) +
          x + y - 1 := by rw [e1, e2]
    _ = (y : Matrix (Fin n) (Fin n) K) * x := by noncomm_ring

end Commuting

section Pattern

variable {K : Type} [Field K] {n : ℕ}

@[expose] def pat (n : ℕ) (j : Fin n) : Bool × Bool :=
  if j.val = 0 then (false, true) else if j.val = 1 then (false, false)
  else if j.val = 2 then (true, false) else (true, true)

theorem pat_eq_ft_iff (j : Fin n) : pat n j = (false, true) ↔ j.val = 0 := by
  unfold pat
  split_ifs <;> simp_all

theorem pat_eq_ff_iff (j : Fin n) : pat n j = (false, false) ↔ j.val = 1 := by
  unfold pat
  split_ifs <;> simp_all

theorem pat_eq_tf_iff (j : Fin n) : pat n j = (true, false) ↔ j.val = 2 := by
  unfold pat
  split_ifs <;> simp_all

theorem pat_eq_tt_iff (j : Fin n) : pat n j = (true, true) ↔ 3 ≤ j.val := by
  unfold pat
  split_ifs <;> simp_all
  omega

theorem card_fin_val_eq {c : ℕ} (hc : c < n) : Nat.card {j : Fin n // j.val = c} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun a b => Subtype.ext (Fin.ext (a.2.trans b.2.symm))⟩, ⟨⟨⟨c, hc⟩, rfl⟩⟩⟩

theorem card_fin_val_lt {m : ℕ} (hm : m ≤ n) : Nat.card {j : Fin n // j.val < m} = m := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Fin.card_filter_val_lt]
  omega

theorem card_fin_val_ge {m : ℕ} (hm : m ≤ n) : Nat.card {j : Fin n // m ≤ j.val} = n - m := by
  have h1 : Fintype.card {j : Fin n // j.val < m} = m := by
    rw [← Nat.card_eq_fintype_card]
    exact card_fin_val_lt hm
  have h2 := Fintype.card_subtype_compl (fun j : Fin n => j.val < m)
  rw [Nat.card_congr (Equiv.subtypeEquivRight
      (fun j : Fin n => (not_lt (a := j.val) (b := m)).symm)),
    Nat.card_eq_fintype_card, h2, h1, Fintype.card_fin]

theorem card_pat_ft (hn : 3 ≤ n) : Nat.card {j : Fin n // pat n j = (false, true)} = 1 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight pat_eq_ft_iff)]
  exact card_fin_val_eq (by omega)

theorem card_pat_ff (hn : 3 ≤ n) : Nat.card {j : Fin n // pat n j = (false, false)} = 1 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight pat_eq_ff_iff)]
  exact card_fin_val_eq (by omega)

theorem card_pat_tf (hn : 3 ≤ n) : Nat.card {j : Fin n // pat n j = (true, false)} = 1 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight pat_eq_tf_iff)]
  exact card_fin_val_eq (by omega)

theorem card_pat_tt (hn : 3 ≤ n) : Nat.card {j : Fin n // pat n j = (true, true)} = n - 3 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight pat_eq_tt_iff)]
  exact card_fin_val_ge hn

theorem diagonal_pat_fst : Matrix.diagonal (fun j : Fin n => signOf K (pat n j).1) =
    negBlock K n 0 := by
  rw [negBlock_eq_diagonal]
  congr 1
  funext j
  unfold pat
  split_ifs <;> simp_all
  omega

theorem diagonal_pat_snd : Matrix.diagonal (fun j : Fin n => signOf K (pat n j).2) =
    negBlock K n 1 := by
  rw [negBlock_eq_diagonal]
  congr 1
  funext j
  unfold pat
  split_ifs <;> simp_all
  omega

end Pattern

section Dichotomy

variable {K : Type} [Field K] {n : ℕ}

theorem inf_eq_bot_or_exists_frame (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n)
    {I₁ I₂ : Matrix (Fin n) (Fin n) K} (h₁ : I₁ * I₁ = 1) (h₂ : I₂ * I₂ = 1)
    (hc : I₁ * I₂ = I₂ * I₁) (hd₁ : finrank K (eigSpace I₁ (-1)) = 2)
    (hd₂ : finrank K (eigSpace I₂ (-1)) = 2) (hne : I₁ ≠ I₂) :
    eigSpace I₁ (-1) ⊓ eigSpace I₂ (-1) = ⊥ ∨
      ∃ P : SL(n, K), I₁ * (P : Matrix (Fin n) (Fin n) K) = P * negBlock K n 0 ∧
        I₂ * (P : Matrix (Fin n) (Fin n) K) = P * negBlock K n 1 := by
  have hf := toLin'_mul_self h₁
  have hg := toLin'_mul_self h₂
  have hfg := toLin'_mul_comm hc
  have hint := isInternal_jointEigenspace h2 hf hg hfg
  set d : Bool × Bool → ℕ := fun s => finrank K (jointEig I₁ I₂ s) with hd
  have E1 : 2 = d (false, true) + d (false, false) := by
    rw [← hd₁]
    exact finrank_eigenspace_eq h2 hg hfg false
  have E2 : 2 = d (true, false) + d (false, false) := by
    rw [← hd₂]
    exact finrank_eigenspace_eq' h2 hf hfg false
  have E3 : n = d (true, true) + d (true, false) + (d (false, true) + d (false, false)) := by
    have := finrank_eq_sum_of_isInternal (jointEig I₁ I₂) hint
    rw [Module.finrank_fin_fun, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool,
      Fintype.sum_bool] at this
    exact this
  have hmm : d (false, false) = 0 ∨ d (false, false) = 1 ∨ d (false, false) = 2 := by omega
  rcases hmm with h0 | h1 | h2'
  · left
    have : jointEig I₁ I₂ (false, false) = ⊥ := Submodule.finrank_eq_zero.mp h0
    exact this
  · right
    refine exists_sl_frame h2 (by omega) h₁ h₂ hc (pat n) ?_ |>.imp fun P hP => ?_
    · rintro ⟨_ | _, _ | _⟩
      · rw [card_pat_ff hn]
        show 1 = d (false, false)
        omega
      · rw [card_pat_ft hn]
        show 1 = d (false, true)
        omega
      · rw [card_pat_tf hn]
        show 1 = d (true, false)
        omega
      · rw [card_pat_tt hn]
        show n - 3 = d (true, true)
        omega
    · rw [diagonal_pat_fst, diagonal_pat_snd] at hP
      exact hP
  · exfalso
    have hz1 : jointEig I₁ I₂ (false, true) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by change d (false, true) = 0; omega)
    have hz2 : jointEig I₁ I₂ (true, false) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by change d (true, false) = 0; omega)
    have := eq_of_jointEigenspace_mixed_eq_bot h2 hf hg hfg hz2 hz1
    exact hne (Matrix.toLin'.injective this)

end Dichotomy

section Generation

variable {K : Type} [Field K] {m : ℕ}

theorem transvection_mem_range_blockSL {o : ℕ} (ho : o + 2 ≤ m) {i j : Fin m} (hij : i ≠ j)
    (hi : o ≤ i.val ∧ i.val < o + 2) (hj : o ≤ j.val ∧ j.val < o + 2) (c : K) :
    Matrix.SpecialLinearGroup.transvection hij c ∈ (blockSL K m 2 o ho).range := by
  have hpq : (⟨i.val - o, by omega⟩ : Fin 2) ≠ ⟨j.val - o, by omega⟩ := by
    intro h
    apply hij
    apply Fin.ext
    have := congrArg Fin.val h
    simp only at this
    omega
  refine ⟨Matrix.SpecialLinearGroup.transvection hpq c, ?_⟩
  apply Subtype.ext
  rw [coe_blockSL, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  ext a b
  rw [blockMat_apply]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff]
  split_ifs <;> simp_all <;> omega

theorem B12_sup_B23 : B12 K ⊔ B23 K = ⊤ := by
  rw [eq_top_iff, ← iSup_fundamentalRootSubgroup_eq_top (m := 2) (F := K)]
  refine iSup_le fun k => iSup_le fun s => ?_
  intro x hx
  fin_cases k <;> cases s <;> simp only [fundamentalRootSubgroup] at hx <;>
    obtain ⟨c, rfl⟩ := (mem_rootSubgroup _ x).mp hx
  · exact Subgroup.mem_sup_left
      (transvection_mem_range_blockSL (by omega) _ (by simp) (by simp) c)
  · exact Subgroup.mem_sup_left
      (transvection_mem_range_blockSL (by omega) _ (by simp) (by simp) c)
  · exact Subgroup.mem_sup_right
      (transvection_mem_range_blockSL (by omega) _ (by simp) (by simp) c)
  · exact Subgroup.mem_sup_right
      (transvection_mem_range_blockSL (by omega) _ (by simp) (by simp) c)

theorem B12_map_blockSL (hn : 3 ≤ m) :
    (B12 K).map (blockSL K m 3 0 (by omega)) = (blockSL K m 2 0 (by omega)).range := by
  rw [B12, ← MonoidHom.range_comp]
  exact congrArg MonoidHom.range (blockSL_comp (K := K) (by omega) (by omega))

theorem B23_map_blockSL (hn : 3 ≤ m) :
    (B23 K).map (blockSL K m 3 0 (by omega)) = (blockSL K m 2 1 (by omega)).range := by
  rw [B23, ← MonoidHom.range_comp]
  exact congrArg MonoidHom.range (blockSL_comp (K := K) (by omega) (by omega))

theorem range_blockSL_three (hn : 3 ≤ m) :
    (blockSL K m 3 0 (by omega)).range =
      (blockSL K m 2 0 (by omega)).range ⊔ (blockSL K m 2 1 (by omega)).range := by
  rw [MonoidHom.range_eq_map, ← B12_sup_B23, Subgroup.map_sup, B12_map_blockSL hn,
    B23_map_blockSL hn]

end Generation

section NonCommuting

variable {K : Type} [Field K] {n : ℕ}

theorem not_comm_blockSL_zero_one (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    ∃ A : SL(2, K), blockSL K n 2 0 (by omega) A * blockSL K n 2 1 (by omega) (-1) ≠
      blockSL K n 2 1 (by omega) (-1) * blockSL K n 2 0 (by omega) A := by
  refine ⟨Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) 1, ?_⟩
  intro h
  have h1 := congr_fun (congr_fun (congrArg (fun g : SL(n, K) => (g : Matrix (Fin n) (Fin n) K)) h)
    ⟨0, by omega⟩) ⟨1, by omega⟩
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL_neg_one, negBlock_eq_diagonal,
    Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  have e : (blockMat n 0 (Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) (1 : K) : Matrix (Fin 2) (Fin 2) K)) ⟨0, by omega⟩
        ⟨1, by omega⟩ = 1 := by
    have := blockMat_apply_blockIdx (m := n) (i := 0) (k := 2) (by omega)
      (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (1 : K) :
        Matrix (Fin 2) (Fin 2) K) 0 1
    simpa [blockIdx, Matrix.SpecialLinearGroup.transvection_coe, Matrix.transvection,
      Matrix.single_apply] using this
  simp only [coe_blockSL, e] at h1
  norm_num at h1
  exact h2 (by linear_combination -h1)

end NonCommuting

section Main

variable {K : Type} [Field K] {n : ℕ}

theorem IsLongRootSL2.mem {hn : 2 ≤ n} {L : Subgroup SL(n, K)} {i : SL(n, K)}
    (h : IsLongRootSL2 hn L i) : i ∈ L := by
  obtain ⟨g, rfl, rfl⟩ := h
  exact Subgroup.mem_map.mpr ⟨_, rootInv_mem_rootSL2 hn, rfl⟩

theorem IsLongRootSL2.mul_self {hn : 2 ≤ n} {L : Subgroup SL(n, K)} {i : SL(n, K)}
    (h : IsLongRootSL2 hn L i) : i * i = 1 := by
  obtain ⟨g, rfl, rfl⟩ := h
  have : rootInv K hn * rootInv K hn = 1 := by
    rw [rootInv, ← map_mul, neg_mul_neg, one_mul, map_one]
  calc g * rootInv K hn * g⁻¹ * (g * rootInv K hn * g⁻¹)
      = g * (rootInv K hn * rootInv K hn) * g⁻¹ := by group
    _ = 1 := by rw [this]; group

theorem IsLongRootSL2.finrank_minusSpace (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n}
    {L : Subgroup SL(n, K)} {i : SL(n, K)} (h : IsLongRootSL2 hn L i) :
    finrank K (minusSpace i) = 2 := by
  obtain ⟨g, -, rfl⟩ := h
  exact finrank_eigSpace_conj_neg_one h2 hn g

theorem linearBlockStandardPair_of_normalized {X : Type} [Group X] {θ : SL(3, K) →* X}
    (hker : θ.ker ≤ Subgroup.center SL(3, K)) {W U V : Subgroup X} (hW : θ.range = W)
    (hU : (B12 K).map θ = U) (hV : (B23 K).map θ = V) : LinearBlockStandardPair K W U V := by
  have e : (MulAut.conj (1 : SL(3, K))⁻¹).toMonoidHom = MonoidHom.id _ := by
    ext x
    simp
  refine ⟨θ, 1, hW, hker, Or.inl ⟨?_, ?_⟩⟩
  · rw [e, Subgroup.map_id]
    exact hU
  · rw [e, Subgroup.map_id]
    exact hV

theorem exists_injective_hom_of_frame (hn : 3 ≤ n) {L₁ L₂ : Subgroup SL(n, K)} (P : SL(n, K))
    (h₁ : L₁ = (blockSL K n 2 0 (by omega)).range.map (MulAut.conj P).toMonoidHom)
    (h₂ : L₂ = (blockSL K n 2 1 (by omega)).range.map (MulAut.conj P).toMonoidHom) :
    ∃ θ : SL(3, K) →* SL(n, K), Function.Injective θ ∧ θ.range = L₁ ⊔ L₂ ∧
      (B12 K).map θ = L₁ ∧ (B23 K).map θ = L₂ := by
  refine ⟨(MulAut.conj P).toMonoidHom.comp (blockSL K n 3 0 (by omega)), ?_, ?_, ?_, ?_⟩
  · exact (MulAut.conj P).injective.comp (blockSL_injective _)
  · rw [MonoidHom.range_comp, range_blockSL_three hn, Subgroup.map_sup, h₁, h₂]
  · rw [← Subgroup.map_map, B12_map_blockSL hn, h₁]
  · rw [← Subgroup.map_map, B23_map_blockSL hn, h₂]

theorem IsLongRootSL2.coe_mul_self {hn : 2 ≤ n} {L : Subgroup SL(n, K)} {i : SL(n, K)}
    (h : IsLongRootSL2 hn L i) :
    (i : Matrix (Fin n) (Fin n) K) * i = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, h.mul_self, Matrix.SpecialLinearGroup.coe_one]

theorem inf_eq_bot_or_exists_conj (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n} (hn3 : 3 ≤ n)
    {L₁ L₂ : Subgroup SL(n, K)} {i₁ i₂ : SL(n, K)} (h₁ : IsLongRootSL2 hn L₁ i₁)
    (h₂ : IsLongRootSL2 hn L₂ i₂) (hc : Commute i₁ i₂) (hne : i₁ ≠ i₂) :
    minusSpace i₁ ⊓ minusSpace i₂ = ⊥ ∨
      ∃ P : SL(n, K),
        L₁ = (blockSL K n 2 0 (by omega)).range.map (MulAut.conj P).toMonoidHom ∧
        L₂ = (blockSL K n 2 1 (by omega)).range.map (MulAut.conj P).toMonoidHom ∧
        i₁ = P * blockSL K n 2 0 (by omega) (-1) * P⁻¹ ∧
        i₂ = P * blockSL K n 2 1 (by omega) (-1) * P⁻¹ := by
  have hcc : (i₁ : Matrix (Fin n) (Fin n) K) * i₂ = i₂ * i₁ := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hc.eq]
  have hne' : (i₁ : Matrix (Fin n) (Fin n) K) ≠ i₂ := fun h => hne (Subtype.ext h)
  rcases inf_eq_bot_or_exists_frame h2 hn3 h₁.coe_mul_self h₂.coe_mul_self hcc
    (h₁.finrank_minusSpace h2) (h₂.finrank_minusSpace h2) hne' with hV | ⟨P, hP1, hP2⟩
  · exact Or.inl hV
  · refine Or.inr ⟨P, ?_, ?_, ?_, ?_⟩
    · rw [h₁.eq_longRootGroup h2, longRootGroup_eq_map_conj_of_mul_eq P hP1,
        range_blockSL_eq_longRootGroup h2 (by omega)]
    · rw [h₂.eq_longRootGroup h2, longRootGroup_eq_map_conj_of_mul_eq P hP2,
        range_blockSL_eq_longRootGroup h2 (by omega)]
    · have : i₁ * P = P * blockSL K n 2 0 (by omega) (-1) := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
          coe_blockSL_neg_one]
        exact hP1
      rw [eq_mul_inv_iff_mul_eq, this]
    · have : i₂ * P = P * blockSL K n 2 1 (by omega) (-1) := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
          coe_blockSL_neg_one]
        exact hP2
      rw [eq_mul_inv_iff_mul_eq, this]

theorem lemma_6_5 (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n} (hn3 : 3 ≤ n)
    {L₁ L₂ : Subgroup SL(n, K)} {i₁ i₂ : SL(n, K)} (h₁ : IsLongRootSL2 hn L₁ i₁)
    (h₂ : IsLongRootSL2 hn L₂ i₂) (hc : Commute i₁ i₂) (hne : i₁ ≠ i₂) :
    ((∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) ∧ minusSpace i₁ ≤ fixSpace i₂ ∧
        minusSpace i₂ ≤ fixSpace i₁ ∧ minusSpace i₁ ⊓ minusSpace i₂ = ⊥) ∨
      (i₂ ∉ Subgroup.centralizer (L₁ : Set SL(n, K)) ∧
        ∃ θ : SL(3, K) →* SL(n, K), Function.Injective θ ∧ θ.range = L₁ ⊔ L₂ ∧
          (B12 K).map θ = L₁ ∧ (B23 K).map θ = L₂) := by
  have hcc : (i₁ : Matrix (Fin n) (Fin n) K) * i₂ = i₂ * i₁ := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hc.eq]
  rcases inf_eq_bot_or_exists_conj h2 hn3 h₁ h₂ hc hne with hV | ⟨P, e₁, e₂, -, hi₂⟩
  · left
    refine ⟨?_, eigSpace_neg_one_le_one h₂.coe_mul_self hcc hV,
      eigSpace_neg_one_le_one h₁.coe_mul_self hcc.symm (by rwa [inf_comm]), hV⟩
    intro x hx y hy
    rw [h₁.eq_longRootGroup h2] at hx
    rw [h₂.eq_longRootGroup h2] at hy
    exact mul_comm_of_inf_eq_bot h2 h₁.coe_mul_self h₂.coe_mul_self hcc hV hx hy
  · right
    refine ⟨?_, exists_injective_hom_of_frame hn3 P e₁ e₂⟩
    intro hmem
    obtain ⟨A, hA⟩ := not_comm_blockSL_zero_one h2 hn3
    have hx : P * blockSL K n 2 0 (by omega) A * P⁻¹ ∈ L₁ := by
      rw [e₁]
      exact Subgroup.mem_map.mpr ⟨_, ⟨A, rfl⟩, rfl⟩
    have h := Subgroup.mem_centralizer_iff.mp hmem _ hx
    rw [hi₂] at h
    apply hA
    calc blockSL K n 2 0 (by omega) A * blockSL K n 2 1 (by omega) (-1)
        = P⁻¹ * (P * blockSL K n 2 0 (by omega) A * P⁻¹ *
            (P * blockSL K n 2 1 (by omega) (-1) * P⁻¹)) * P := by group
      _ = P⁻¹ * (P * blockSL K n 2 1 (by omega) (-1) * P⁻¹ *
            (P * blockSL K n 2 0 (by omega) A * P⁻¹)) * P := by rw [h]
      _ = blockSL K n 2 1 (by omega) (-1) * blockSL K n 2 0 (by omega) A := by group

theorem mem_centralizer_iff_forall_comm (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n} (hn3 : 3 ≤ n)
    {L₁ L₂ : Subgroup SL(n, K)} {i₁ i₂ : SL(n, K)} (h₁ : IsLongRootSL2 hn L₁ i₁)
    (h₂ : IsLongRootSL2 hn L₂ i₂) (hc : Commute i₁ i₂) (hne : i₁ ≠ i₂) :
    i₂ ∈ Subgroup.centralizer (L₁ : Set SL(n, K)) ↔ ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x := by
  constructor
  · intro hmem
    rcases lemma_6_5 h2 hn3 h₁ h₂ hc hne with h | ⟨hnot, -⟩
    · exact h.1
    · exact absurd hmem hnot
  · intro h
    exact Subgroup.mem_centralizer_iff.mpr fun x hx => h x hx i₂ h₂.mem

theorem forall_comm_of_mem_centralizer (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n} (hn3 : 3 ≤ n)
    {L₁ L₂ : Subgroup SL(n, K)} {i₁ i₂ : SL(n, K)} (h₁ : IsLongRootSL2 hn L₁ i₁)
    (h₂ : IsLongRootSL2 hn L₂ i₂) (hc : Commute i₁ i₂) (hne : i₁ ≠ i₂)
    (hmem : i₂ ∈ Subgroup.centralizer (L₁ : Set SL(n, K))) : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x :=
  (mem_centralizer_iff_forall_comm h2 hn3 h₁ h₂ hc hne).mp hmem

theorem linearBlockStandardPair_of_not_mem_centralizer (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n}
    (hn3 : 3 ≤ n) {L₁ L₂ : Subgroup SL(n, K)} {i₁ i₂ : SL(n, K)} (h₁ : IsLongRootSL2 hn L₁ i₁)
    (h₂ : IsLongRootSL2 hn L₂ i₂) (hc : Commute i₁ i₂) (hne : i₁ ≠ i₂)
    (hnot : i₂ ∉ Subgroup.centralizer (L₁ : Set SL(n, K))) :
    LinearBlockStandardPair K (L₁ ⊔ L₂) L₁ L₂ := by
  rcases lemma_6_5 h2 hn3 h₁ h₂ hc hne with ⟨hcomm, -⟩ | ⟨-, θ, hinj, hrange, hU, hV⟩
  · exact absurd ((mem_centralizer_iff_forall_comm h2 hn3 h₁ h₂ hc hne).mpr hcomm) hnot
  · exact linearBlockStandardPair_of_normalized
      (by rw [(MonoidHom.ker_eq_bot_iff θ).mpr hinj]; exact bot_le) hrange hU hV

theorem commute_or_linearBlockStandardPair (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n} (hn3 : 3 ≤ n)
    {L₁ L₂ : Subgroup SL(n, K)} {i₁ i₂ : SL(n, K)} (h₁ : IsLongRootSL2 hn L₁ i₁)
    (h₂ : IsLongRootSL2 hn L₂ i₂) (hc : Commute i₁ i₂) (hne : i₁ ≠ i₂) :
    (∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) ∨
      (i₂ ∉ Subgroup.centralizer (L₁ : Set SL(n, K)) ∧
        LinearBlockStandardPair K (L₁ ⊔ L₂) L₁ L₂) := by
  by_cases hmem : i₂ ∈ Subgroup.centralizer (L₁ : Set SL(n, K))
  · exact Or.inl ((mem_centralizer_iff_forall_comm h2 hn3 h₁ h₂ hc hne).mp hmem)
  · exact Or.inr ⟨hmem, linearBlockStandardPair_of_not_mem_centralizer h2 hn3 h₁ h₂ hc hne hmem⟩

theorem linearBlockStandardPair_map {X Y : Type} [Group X] [Group Y] {W U V : Subgroup X}
    (h : LinearBlockStandardPair K W U V) (φ : X →* Y) (hφ : Function.Injective φ) :
    LinearBlockStandardPair K (W.map φ) (U.map φ) (V.map φ) := by
  obtain ⟨θ, c, hrange, hker, h'⟩ := h
  refine ⟨φ.comp θ, c, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrange]
  · rwa [MonoidHom.ker_comp_of_injective θ φ hφ]
  · rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩
    · right
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩

end Main

end CFSG.ClassicalInvolution.Models
