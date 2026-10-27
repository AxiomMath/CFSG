module

public import CFSG.ClassicalInvolution.Models.UnitaryPairs.RootSU2
public import CFSG.ClassicalInvolution.Phan.Standard

public section

namespace CFSG.ClassicalInvolution.ModelFacts.TG3

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models

section Block

variable {F : Type*} [Field F] {m k k' i i' : ℕ}

theorem blockSel_transpose_mul_blockSel_eq_zero (h : i + k ≤ i') :
    (blockSel F m k i)ᵀ * blockSel F m k' i' = 0 := by
  ext j j'
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, blockSel_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  have hj := j.isLt
  split_ifs with h1 h2
  · omega
  all_goals simp

theorem blockMat_mul_comm_of_disjoint (h : i + k ≤ i') (A : Matrix (Fin k) (Fin k) F)
    (B : Matrix (Fin k') (Fin k') F) :
    blockMat m i A * blockMat m i' B = blockMat m i' B * blockMat m i A := by
  have h0 := blockSel_transpose_mul_blockSel_eq_zero (F := F) (m := m) (k' := k') h
  have h0' : (blockSel F m k' i')ᵀ * blockSel F m k i = 0 := by
    have := congrArg Matrix.transpose h0
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at this
  unfold blockMat
  set L := blockSel F m k i
  set L' := blockSel F m k' i'
  set E := L * (A - 1) * Lᵀ
  set E' := L' * (B - 1) * L'ᵀ
  have e1 : E * E' = 0 := by
    calc E * E' = L * (A - 1) * (Lᵀ * L') * (B - 1) * L'ᵀ := by
          simp only [E, E', Matrix.mul_assoc]
      _ = 0 := by rw [h0]; simp
  have e2 : E' * E = 0 := by
    calc E' * E = L' * (B - 1) * (L'ᵀ * L) * (A - 1) * Lᵀ := by
          simp only [E, E', Matrix.mul_assoc]
      _ = 0 := by rw [h0']; simp
  have p1 : (1 + E) * (1 + E') = 1 + E + E' + E * E' := by noncomm_ring
  have p2 : (1 + E') * (1 + E) = 1 + E' + E + E' * E := by noncomm_ring
  rw [p1, p2, e1, e2, add_zero, add_zero, add_assoc, add_assoc, add_comm E E']

theorem blockMat_mul_diagonal_comm_of_const (v : Fin m → F) (d : F)
    (hv : ∀ a : Fin m, i ≤ a.val → a.val < i + k → v a = d) (A : Matrix (Fin k) (Fin k) F) :
    blockMat m i A * Matrix.diagonal v = Matrix.diagonal v * blockMat m i A := by
  have hL1 : Matrix.diagonal v * blockSel F m k i = d • blockSel F m k i := by
    ext a j
    rw [Matrix.diagonal_mul, Matrix.smul_apply, blockSel_apply]
    by_cases h : a.val = i + j.val
    · have hj := j.isLt
      have hva := hv a (by omega) (by omega)
      simp [h, hva]
    · simp [h]
  have hL2 : (blockSel F m k i)ᵀ * Matrix.diagonal v = d • (blockSel F m k i)ᵀ := by
    have := congrArg Matrix.transpose hL1
    rwa [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.transpose_smul] at this
  unfold blockMat
  set L := blockSel F m k i
  have e1 : (L * (A - 1) * Lᵀ) * Matrix.diagonal v = d • (L * (A - 1) * Lᵀ) := by
    rw [Matrix.mul_assoc, hL2, Matrix.mul_smul, Matrix.mul_assoc]
  have e2 : Matrix.diagonal v * (L * (A - 1) * Lᵀ) = d • (L * (A - 1) * Lᵀ) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hL1, Matrix.smul_mul, Matrix.smul_mul]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, e1, e2]

theorem blockMat_diagonal_zero (x y : F) :
    blockMat 4 0 (Matrix.diagonal ![x, y]) = Matrix.diagonal ![x, y, 1, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blockMat, blockSel, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply,
      Matrix.one_apply, Matrix.sub_apply]

theorem blockMat_diagonal_two (x y : F) :
    blockMat 4 2 (Matrix.diagonal ![x, y]) = Matrix.diagonal ![1, 1, x, y] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blockMat, blockSel, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply,
      Matrix.one_apply, Matrix.sub_apply]

end Block

section Diag2

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Module

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_su_two_diag (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0) {c : K}
    (hc : c * c = -1) (hσc : unitaryInvolution K p f c = -c) (A : Su K p f 2)
    (hA : suMat A * suMat A = -1) :
    ∃ U : Su K p f 2, suMat A * suMat U = suMat U * Matrix.diagonal ![c, -c] := by
  classical
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  set M : Matrix (Fin 2) (Fin 2) K := suMat A with hM
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact one_ne_zero (neg_eq_zero.mp hc.symm)
  have h2c : (2 : K) * c ≠ 0 := mul_ne_zero h2 hc0
  have hMv : ∀ v, M *ᵥ (M *ᵥ v) = -v := fun v => by
    rw [Matrix.mulVec_mulVec, hA, Matrix.neg_mulVec, Matrix.one_mulVec]
  let E : Bool → Submodule K (Fin 2 → K) := fun b => eigSpace M (if b then c else -c)
  have hEt : ∀ v, v ∈ E true ↔ M *ᵥ v = c • v := fun v => mem_eigSpace
  have hEf : ∀ v, v ∈ E false ↔ M *ᵥ v = (-c) • v := fun v => mem_eigSpace
  have hmemt : ∀ v, M *ᵥ v + c • v ∈ E true := fun v => by
    rw [hEt, Matrix.mulVec_add, Matrix.mulVec_smul, hMv, smul_add, smul_smul, hc]
    module
  have hmemf : ∀ v, M *ᵥ v - c • v ∈ E false := fun v => by
    rw [hEf, Matrix.mulVec_sub, Matrix.mulVec_smul, hMv, smul_sub, smul_smul, neg_mul, hc]
    module
  have hdec : ∀ v, v = ((2 * c)⁻¹) • (M *ᵥ v + c • v) + (-(2 * c)⁻¹) • (M *ᵥ v - c • v) :=
    fun v => by
    have : (2 * c) * (2 * c)⁻¹ = 1 := mul_inv_cancel₀ h2c
    calc v = ((2 * c) * (2 * c)⁻¹) • v := by rw [this, one_smul]
      _ = _ := by module
  have hE : ⨆ b, E b = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [hdec v]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem true (hmemt v)))
      (Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem false (hmemf v)))
  have hneg1 : (-1 : K) ≠ 1 := neg_one_ne_one_of_two_ne_zero h2
  have horth : ∀ s t, s ≠ t → Orth (unitaryInvolution K p f) (E s) (E t) := by
    intro s t hst v hv w hw
    cases s <;> cases t
    · exact absurd rfl hst
    · refine herm_eq_zero_of_eigen A ((hEf v).mp hv) ((hEt w).mp hw) ?_
      rw [map_neg, hσc, neg_neg, hc]
      exact hneg1
    · refine herm_eq_zero_of_eigen A ((hEt v).mp hv) ((hEf w).mp hw) ?_
      rw [hσc, neg_mul_neg, hc]
      exact hneg1
    · exact absurd rfl hst
  have hnd : ∀ s, Nondeg (unitaryInvolution K p f) (E s) :=
    nondeg_of_orth_of_iSup_eq_top E hE horth
  have hbot : E true ⊓ E false = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨h1, h2'⟩ := Submodule.mem_inf.mp hv
    rw [hEt] at h1
    rw [hEf] at h2'
    have h3 : ((2 * c)) • v = 0 := by
      have := h1.symm.trans h2'
      calc (2 * c) • v = c • v - (-c) • v := by module
        _ = 0 := by rw [← this]; exact sub_self _
    exact (Submodule.mem_bot K).mpr ((smul_eq_zero.mp h3).resolve_left h2c)
  have hsup : E true ⊔ E false = ⊤ := by
    rw [← hE, iSup_bool_eq]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (E true) (E false)
  rw [hsup, hbot, finrank_top, finrank_bot, Module.finrank_fin_fun] at hdim
  have hdet : M.det = 1 := det_suMat A
  have hne : ∀ e : K, e * e = -1 → (∀ v, M *ᵥ v = e • v) → False := by
    intro e he hall
    have hMe : M = e • (1 : Matrix (Fin 2) (Fin 2) K) := by
      ext a j
      have := congr_fun (hall (Pi.single j 1)) a
      rw [Matrix.mulVec_single_one] at this
      simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this
    rw [hMe, Matrix.det_smul, Matrix.det_one, Fintype.card_fin] at hdet
    apply h2
    linear_combination he - hdet
  have hd1 : finrank K (E true) ≠ 0 := by
    intro h0
    rw [Submodule.finrank_eq_zero] at h0
    refine hne (-c) (by linear_combination hc) fun v => ?_
    have := hmemt v
    rw [h0, Submodule.mem_bot] at this
    exact (neg_smul c v ▸ eq_neg_of_add_eq_zero_left this)
  have hd2 : finrank K (E false) ≠ 0 := by
    intro h0
    rw [Submodule.finrank_eq_zero] at h0
    refine hne c hc fun v => ?_
    have := hmemf v
    rw [h0, Submodule.mem_bot] at this
    exact sub_eq_zero.mp this
  have hε : ∀ s, Nat.card {j : Fin 2 // (![true, false] : Fin 2 → Bool) j = s} =
      finrank K (E s) := by
    intro s
    cases s
    · have : finrank K (E false) = 1 := by omega
      rw [this, Nat.card_eq_fintype_card]
      decide
    · have : finrank K (E true) = 1 := by omega
      rw [this, Nat.card_eq_fintype_card]
      decide
  obtain ⟨g, hg⟩ := exists_su_adapted hσ (by norm_num : 0 < 2) E hnd horth ![true, false] hε
  refine ⟨g, ?_⟩
  ext a j
  rw [Matrix.mul_diagonal]
  have h1 := congr_fun (mem_eigSpace.mp (hg j)) a
  rw [suMat_smul, Matrix.mulVec_single_one] at h1
  fin_cases j
  · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using h1
  · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using h1

end Diag2

section Std

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Module

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem su4_std_gen (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {c : K}
    (hc : c * c = -1) (hσc : unitaryInvolution K p f c = -c) (A₁ A₂ : Su K p f 2)
    (hA₁ : A₁ * A₁ = negOneSU K p f) (hA₂ : A₂ * A₂ = negOneSU K p f) :
    Subgroup.centralizer ({(blockEmb K p f 4 2 0 (by norm_num) (negOneSU K p f))} :
        Set (Su K p f 4)) ⊔
      Subgroup.centralizer ({(blockEmb K p f 4 2 0 (by norm_num) A₁ *
        blockEmb K p f 4 2 2 (by norm_num) A₂)} : Set (Su K p f 4)) = ⊤ := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp
  have hq : p ^ f ≠ 2 := prime_pow_ne_two_of_ne_two hp f
  set b0 := blockEmb K p f 4 2 0 (by norm_num : 0 + 2 ≤ 4) with hb0
  set b1 := blockEmb K p f 4 2 1 (by norm_num : 1 + 2 ≤ 4) with hb1
  set b2 := blockEmb K p f 4 2 2 (by norm_num : 2 + 2 ≤ 4) with hb2
  have hcomm : ∀ X Y : Su K p f 2, b0 X * b2 Y = b2 Y * b0 X := fun X Y =>
    suMat_injective (blockMat_mul_comm_of_disjoint (by norm_num) _ _)
  have hc' : (-c) * (-c) = -1 := by rw [neg_mul_neg, hc]
  have hσc' : unitaryInvolution K p f (-c) = -(-c) := by rw [map_neg, hσc]
  obtain ⟨U₁, hU₁⟩ := exists_su_two_diag hK h2 hc hσc A₁ (by rw [← suMat_mul, hA₁, suMat_negOneSU])
  obtain ⟨U₂, hU₂⟩ := exists_su_two_diag hK h2 hc' hσc' A₂
    (by rw [← suMat_mul, hA₂, suMat_negOneSU])
  set Λ₁ : Su K p f 2 := U₁⁻¹ * A₁ * U₁ with hΛ₁
  set Λ₂ : Su K p f 2 := U₂⁻¹ * A₂ * U₂ with hΛ₂
  have hΛ₁m : suMat Λ₁ = Matrix.diagonal ![c, -c] := by
    have : suMat Λ₁ = suMat U₁⁻¹ * (suMat A₁ * suMat U₁) := by
      simp only [hΛ₁, suMat_mul, Matrix.mul_assoc]
    rw [this, hU₁, ← Matrix.mul_assoc, suMat_inv_mul_suMat, Matrix.one_mul]
  have hΛ₂m : suMat Λ₂ = Matrix.diagonal ![-c, -(-c)] := by
    have : suMat Λ₂ = suMat U₂⁻¹ * (suMat A₂ * suMat U₂) := by
      simp only [hΛ₂, suMat_mul, Matrix.mul_assoc]
    rw [this, hU₂, ← Matrix.mul_assoc, suMat_inv_mul_suMat, Matrix.one_mul]
  have hAU₁ : A₁ * U₁ = U₁ * Λ₁ := by rw [hΛ₁]; group
  have hAU₂ : A₂ * U₂ = U₂ * Λ₂ := by rw [hΛ₂]; group
  set D := b0 (negOneSU K p f) with hD
  set J' := b0 A₁ * b2 A₂ with hJ'
  set g := b0 U₁ * b2 U₂ with hg
  set J₀ := b0 Λ₁ * b2 Λ₂ with hJ₀
  have hmul : ∀ X X' Y Y' : Su K p f 2, (b0 X * b2 Y) * (b0 X' * b2 Y') =
      b0 (X * X') * b2 (Y * Y') := fun X X' Y Y' => by
    rw [map_mul, map_mul]
    calc (b0 X * b2 Y) * (b0 X' * b2 Y') = b0 X * (b2 Y * b0 X') * b2 Y' := by group
      _ = b0 X * (b0 X' * b2 Y) * b2 Y' := by rw [← hcomm X' Y]
      _ = _ := by group
  have hJ'g : J' * g = g * J₀ := by
    rw [hJ', hg, hJ₀, hmul, hmul, hAU₁, hAU₂]
  have hb0D : ∀ X : Su K p f 2, b0 X * D = D * b0 X := fun X => by
    rw [hD, ← map_mul, ← map_mul, negOneSU_comm]
  have hb2D : ∀ Y : Su K p f 2, b2 Y * D = D * b2 Y := fun Y => by
    rw [hD, ← hcomm]
  have hgD : g * D = D * g := by
    rw [hg, mul_assoc, hb2D, ← mul_assoc, hb0D, mul_assoc]
  set H : Subgroup (Su K p f 4) := Subgroup.centralizer ({D} : Set (Su K p f 4)) ⊔
    Subgroup.centralizer ({J'} : Set (Su K p f 4)) with hH
  have hgH : g ∈ H := Subgroup.mem_sup_left (Subgroup.mem_centralizer_singleton_iff.mpr hgD)
  have hJ₀H : Subgroup.centralizer ({J₀} : Set (Su K p f 4)) ≤ H := by
    intro y hy
    have hy' := Subgroup.mem_centralizer_singleton_iff.mp hy
    have hJ'eq : J' = g * J₀ * g⁻¹ := by rw [← hJ'g]; group
    have hconj : g * y * g⁻¹ ∈ Subgroup.centralizer ({J'} : Set (Su K p f 4)) := by
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      rw [hJ'eq]
      calc g * y * g⁻¹ * (g * J₀ * g⁻¹) = g * (y * J₀) * g⁻¹ := by group
        _ = g * (J₀ * y) * g⁻¹ := by rw [hy']
        _ = g * J₀ * g⁻¹ * (g * y * g⁻¹) := by group
    have hconjH : g * y * g⁻¹ ∈ H := Subgroup.mem_sup_right hconj
    have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
    rw [this]
    exact H.mul_mem (H.mul_mem (H.inv_mem hgH) hconjH) hgH
  have hJ₀m : suMat J₀ = Matrix.diagonal ![c, -c, -c, c] := by
    have : suMat J₀ = blockMat 4 0 (suMat Λ₁) * blockMat 4 2 (suMat Λ₂) := rfl
    rw [this, hΛ₁m, hΛ₂m, blockMat_diagonal_zero, blockMat_diagonal_two,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    fin_cases a <;> simp
  have hb1J₀ : ∀ X : Su K p f 2, b1 X * J₀ = J₀ * b1 X := fun X => by
    refine suMat_injective ?_
    change suMat (b1 X) * suMat J₀ = suMat J₀ * suMat (b1 X)
    rw [hJ₀m]
    exact blockMat_mul_diagonal_comm_of_const (i := 1) (k := 2) ![c, -c, -c, c] (-c)
      (fun a ha1 ha2 => by fin_cases a <;> simp_all) (suMat X)
  have hM : Subgroup.centralizer ({D} : Set (Su K p f 4)) ⊔
      Subgroup.centralizer ({J₀} : Set (Su K p f 4)) = ⊤ := by
    rw [eq_top_iff, ← iSup_range_blockEmb2 hK hq 3]
    refine iSup_le fun i => ?_
    fin_cases i
    · change (blockEmb K p f 4 2 0 (by norm_num)).range ≤ _
      rintro _ ⟨X, rfl⟩
      exact Subgroup.mem_sup_left (Subgroup.mem_centralizer_singleton_iff.mpr (hb0D X))
    · change (blockEmb K p f 4 2 1 (by norm_num)).range ≤ _
      rintro _ ⟨X, rfl⟩
      exact Subgroup.mem_sup_right (Subgroup.mem_centralizer_singleton_iff.mpr (hb1J₀ X))
    · change (blockEmb K p f 4 2 2 (by norm_num)).range ≤ _
      rintro _ ⟨X, rfl⟩
      exact Subgroup.mem_sup_left (Subgroup.mem_centralizer_singleton_iff.mpr (hb2D X))
  rw [eq_top_iff, ← hM]
  exact sup_le le_sup_left hJ₀H

end Std

end CFSG.ClassicalInvolution.ModelFacts.TG3
