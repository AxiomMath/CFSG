module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorField
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorElementary
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityUnitary
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearGraphFieldDescent
public import CFSG.ClassicalGroups.Unitary.Simple

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.OutcomeLocal

section Signs

variable {K : Type} [Field K] {n : ℕ}

@[expose] def sgnMat (S : Finset (Fin n)) : Matrix (Fin n) (Fin n) K :=
  diagonal fun i => if i ∈ S then -1 else 1

theorem sgnMat_mul_sgnMat (S T : Finset (Fin n)) :
    (sgnMat S : Matrix (Fin n) (Fin n) K) * sgnMat T = sgnMat (symmDiff S T) := by
  rw [sgnMat, sgnMat, sgnMat, diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT, Finset.mem_symmDiff]

theorem sgnMat_mul_self (S : Finset (Fin n)) :
    (sgnMat S : Matrix (Fin n) (Fin n) K) * sgnMat S = 1 := by
  rw [sgnMat_mul_sgnMat, symmDiff_self, Finset.bot_eq_empty, sgnMat]
  simp [diagonal_one]

theorem sgnMat_comm (S T : Finset (Fin n)) :
    (sgnMat S : Matrix (Fin n) (Fin n) K) * sgnMat T = sgnMat T * sgnMat S := by
  rw [sgnMat_mul_sgnMat, sgnMat_mul_sgnMat, symmDiff_comm]

theorem det_sgnMat (S : Finset (Fin n)) :
    (sgnMat S : Matrix (Fin n) (Fin n) K).det = (-1) ^ S.card := by
  rw [sgnMat, det_diagonal, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
    Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem transpose_sgnMat (S : Finset (Fin n)) :
    (sgnMat S : Matrix (Fin n) (Fin n) K)ᵀ = sgnMat S := diagonal_transpose _

theorem map_sgnMat (φ : K →+* K) (S : Finset (Fin n)) :
    (sgnMat S : Matrix (Fin n) (Fin n) K).map φ = sgnMat S := by
  rw [sgnMat, diagonal_map (map_zero φ)]
  congr 1
  funext i
  split_ifs <;> simp

theorem sgnMat_eq_scalar (h2 : (2 : K) ≠ 0) {S : Finset (Fin n)} {c : K}
    (h : (sgnMat S : Matrix (Fin n) (Fin n) K) = scalar (Fin n) c) {i j : Fin n} (hi : i ∈ S)
    (hj : j ∉ S) : False := by
  have hii := congrFun (congrFun h i) i
  have hjj := congrFun (congrFun h j) j
  simp only [sgnMat, diagonal_apply_eq, scalar_apply, hi, hj, ↓reduceIte] at hii hjj
  apply h2
  linear_combination hjj - hii

end Signs

section Unitary

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

@[expose] def sgnGL (S : Finset (Fin n)) : GL (Fin n) K :=
  ⟨sgnMat S, sgnMat S, sgnMat_mul_self S, sgnMat_mul_self S⟩

include h in
theorem sgnGL_mem_unitarySU {S : Finset (Fin n)} (hS : Even S.card) :
    sgnGL S ∈ unitarySU p f K n := by
  rw [mem_unitarySU_iff h]
  refine ⟨?_, ?_⟩
  · change (sgnMat S : Matrix (Fin n) (Fin n) K).det = 1
    rw [det_sgnMat, hS.neg_one_pow]
  · change ((sgnMat S : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * sgnMat S = 1
    rw [map_sgnMat, transpose_sgnMat, sgnMat_mul_self]

theorem unitaryProj_ne_one {g : unitarySU p f K n}
    (hg : ∀ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ scalar (Fin n) c) :
    unitaryProj h n g ≠ 1 := by
  intro h1
  have hk : g ∈ (unitaryProj h n).ker := h1
  rw [ker_unitaryProj, mem_unitaryScalars] at hk
  obtain ⟨c, -, -, hc⟩ := hk
  apply hg c
  rw [hc]
  rfl

theorem unitaryProj_ne_unitaryProj {g g' : unitarySU p f K n} (hg' : g' * g' = 1)
    (hgg : ∀ c : K, (((g * g' : unitarySU p f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠
      scalar (Fin n) c) :
    unitaryProj h n g ≠ unitaryProj h n g' := by
  intro heq
  apply unitaryProj_ne_one h hgg
  rw [map_mul, heq, ← map_mul, hg', map_one]

end Unitary

section Perm

variable {K : Type} [Field K] {n : ℕ}

theorem permMatrix_apply (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (σ.permMatrix K) i j = if σ i = j then 1 else 0 := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  simp

theorem permMatrix_mul_diagonal (σ : Equiv.Perm (Fin n)) (d : Fin n → K) :
    σ.permMatrix K * diagonal d = diagonal (d ∘ σ) * σ.permMatrix K := by
  ext i j
  rw [mul_diagonal, diagonal_mul, permMatrix_apply]
  split_ifs with h
  · rw [Function.comp_apply, h, one_mul, mul_one]
  · rw [mul_zero, zero_mul]

theorem map_permMatrix (φ : K →+* K) (σ : Equiv.Perm (Fin n)) :
    (σ.permMatrix K).map φ = σ.permMatrix K := by
  ext i j
  rw [map_apply, permMatrix_apply]
  split_ifs <;> simp

theorem ne_scalar_of_offDiag {M : Matrix (Fin n) (Fin n) K} {i j : Fin n} (hij : i ≠ j)
    (h : M i j ≠ 0) (c : K) : M ≠ scalar (Fin n) c := by
  intro hM
  apply h
  rw [hM, scalar_apply, diagonal_apply_ne _ hij]

end Perm

section UnitaryEight

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

include h in
theorem exists_elementary_unitaryPSU_five (hp2 : p ≠ 2) {n : ℕ} (hn : 5 ≤ n) :
    ∃ E : Subgroup (unitaryPSU h n), IsElementaryAbelian 2 E ∧ 4 < Nat.card E := by
  classical
  have := h.finite
  have : CharP K p := h.charP
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  set i0 : Fin n := ⟨0, by omega⟩
  set i1 : Fin n := ⟨1, by omega⟩
  set i2 : Fin n := ⟨2, by omega⟩
  set i3 : Fin n := ⟨3, by omega⟩
  set i4 : Fin n := ⟨4, by omega⟩
  have hne : ∀ a b : Fin n, a.val ≠ b.val → a ≠ b := fun a b hab h => hab (by rw [h])
  have h01 := hne i0 i1 (by simp [i0, i1])
  have h02 := hne i0 i2 (by simp [i0, i2])
  have h03 := hne i0 i3 (by simp [i0, i3])
  have h04 := hne i0 i4 (by simp [i0, i4])
  have h12 := hne i1 i2 (by simp [i1, i2])
  have h13 := hne i1 i3 (by simp [i1, i3])
  have h14 := hne i1 i4 (by simp [i1, i4])
  have h23 := hne i2 i3 (by simp [i2, i3])
  have h24 := hne i2 i4 (by simp [i2, i4])
  have h34 := hne i3 i4 (by simp [i3, i4])
  set S₁ : Finset (Fin n) := {i0, i1}
  set S₂ : Finset (Fin n) := {i1, i2}
  set S₃ : Finset (Fin n) := {i2, i3}
  have hS₁ : Even S₁.card := by rw [Finset.card_pair h01]; exact even_two
  have hS₂ : Even S₂.card := by rw [Finset.card_pair h12]; exact even_two
  have hS₃ : Even S₃.card := by rw [Finset.card_pair h23]; exact even_two
  set g₁ : unitarySU p f K n := ⟨sgnGL S₁, sgnGL_mem_unitarySU h hS₁⟩
  set g₂ : unitarySU p f K n := ⟨sgnGL S₂, sgnGL_mem_unitarySU h hS₂⟩
  set g₃ : unitarySU p f K n := ⟨sgnGL S₃, sgnGL_mem_unitarySU h hS₃⟩
  have hv₁ : ((g₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = sgnMat S₁ := rfl
  have hv₂ : ((g₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = sgnMat S₂ := rfl
  have hv₃ : ((g₃ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = sgnMat S₃ := rfl
  have hsq : ∀ g : unitarySU p f K n, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (g : GL (Fin n) K) = 1 → g * g = 1 := fun g hg => Subtype.ext (Units.ext hg)
  have hcm : ∀ g g' : unitarySU p f K n, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (g' : GL (Fin n) K) = (g' : GL (Fin n) K) * (g : GL (Fin n) K) → g * g' = g' * g :=
    fun g g' hg => Subtype.ext (Units.ext hg)
  have hg₁ : g₁ * g₁ = 1 := hsq _ (sgnMat_mul_self S₁)
  have hg₂ : g₂ * g₂ = 1 := hsq _ (sgnMat_mul_self S₂)
  have hg₃ : g₃ * g₃ = 1 := hsq _ (sgnMat_mul_self S₃)
  have hc₁₂ : g₁ * g₂ = g₂ * g₁ := hcm _ _ (sgnMat_comm S₁ S₂)
  have hc₁₃ : g₁ * g₃ = g₃ * g₁ := hcm _ _ (sgnMat_comm S₁ S₃)
  have hc₂₃ : g₂ * g₃ = g₃ * g₂ := hcm _ _ (sgnMat_comm S₂ S₃)
  have hns : ∀ (T : Finset (Fin n)) (g : unitarySU p f K n),
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = sgnMat T → ∀ {i j : Fin n}, i ∈ T →
        j ∉ T → ∀ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ scalar (Fin n) c :=
    fun T g hg i j hi hj c hc => sgnMat_eq_scalar h2 (hg.symm.trans hc) hi hj
  have hm : ∀ g g' : unitarySU p f K n, (((g * g' : unitarySU p f K n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (g : GL (Fin n) K) * (g' : GL (Fin n) K) := fun _ _ => rfl
  set π := unitaryProj h n
  refine exists_elementary_of_commuting (x := π g₁) (y := π g₂) (z := π g₃)
    (by rw [← map_mul, hg₁, map_one]) (by rw [← map_mul, hg₂, map_one])
    (by rw [← map_mul, hg₃, map_one])
    (by change π g₁ * π g₂ = π g₂ * π g₁; rw [← map_mul, hc₁₂, map_mul])
    (by change π g₁ * π g₃ = π g₃ * π g₁; rw [← map_mul, hc₁₃, map_mul])
    (by change π g₂ * π g₃ = π g₃ * π g₂; rw [← map_mul, hc₂₃, map_mul]) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact unitaryProj_ne_one h (hns S₁ g₁ rfl (i := i0) (j := i4) (by simp [S₁])
      (by simp [S₁, h04.symm, h14.symm]))
  · exact unitaryProj_ne_one h (hns S₂ g₂ rfl (i := i1) (j := i4) (by simp [S₂])
      (by simp [S₂, h14.symm, h24.symm]))
  · refine unitaryProj_ne_unitaryProj h hg₂ (hns (symmDiff S₁ S₂) _ ?_ (i := i0) (j := i4) ?_ ?_)
    · rw [hm, hv₁, hv₂, sgnMat_mul_sgnMat]
    · simp [S₁, S₂, Finset.mem_symmDiff, h01, h02]
    · simp [S₁, S₂, Finset.mem_symmDiff, h04.symm, h14.symm, h24.symm]
  · exact unitaryProj_ne_one h (hns S₃ g₃ rfl (i := i2) (j := i4) (by simp [S₃])
      (by simp [S₃, h24.symm, h34.symm]))
  · refine unitaryProj_ne_unitaryProj h hg₁ (hns (symmDiff S₃ S₁) _ ?_ (i := i0) (j := i4) ?_ ?_)
    · rw [hm, hv₃, hv₁, sgnMat_mul_sgnMat]
    · simp [S₁, S₃, Finset.mem_symmDiff, h02, h03]
    · simp [S₁, S₃, Finset.mem_symmDiff, h04.symm, h14.symm, h24.symm, h34.symm]
  · refine unitaryProj_ne_unitaryProj h hg₂ (hns (symmDiff S₃ S₂) _ ?_ (i := i1) (j := i4) ?_ ?_)
    · rw [hm, hv₃, hv₂, sgnMat_mul_sgnMat]
    · simp [S₂, S₃, Finset.mem_symmDiff, h12, h13]
    · simp [S₂, S₃, Finset.mem_symmDiff, h14.symm, h24.symm, h34.symm]
  · rw [← map_mul]
    have hg₁₂ : g₁ * g₂ * (g₁ * g₂) = 1 := by
      rw [show g₁ * g₂ * (g₁ * g₂) = g₁ * g₁ * (g₂ * g₂) by
        rw [mul_assoc, ← mul_assoc g₂, ← hc₁₂, mul_assoc, mul_assoc], hg₁, hg₂, one_mul]
    refine unitaryProj_ne_unitaryProj h hg₁₂
      (hns (symmDiff S₃ (symmDiff S₁ S₂)) _ ?_ (i := i0) (j := i4) ?_ ?_)
    · rw [hm, hm, hv₃, hv₁, hv₂, sgnMat_mul_sgnMat, sgnMat_mul_sgnMat]
    · simp [S₁, S₂, S₃, Finset.mem_symmDiff, h01, h02, h03]
    · simp [S₁, S₂, S₃, Finset.mem_symmDiff, h04.symm, h14.symm, h24.symm, h34.symm]

include h in
theorem exists_elementary_unitaryPSU_four (hp2 : p ≠ 2) :
    ∃ E : Subgroup (unitaryPSU h 4), IsElementaryAbelian 2 E ∧ 4 < Nat.card E := by
  classical
  have := h.finite
  have : CharP K p := h.charP
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  set σX : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3 with hσX
  set σY : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3 with hσY
  have hXX : σX * σX = 1 := by decide
  have hYY : σY * σY = 1 := by decide
  have hXY : σX * σY = σY * σX := by decide
  have hsX : Equiv.Perm.sign σX = 1 := by decide
  have hsY : Equiv.Perm.sign σY = 1 := by decide
  have hperm : ∀ σ : Equiv.Perm (Fin 4), σ * σ = 1 → Equiv.Perm.sign σ = 1 →
      ∃ g : unitarySU p f K 4, ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        σ.permMatrix K := by
    intro σ hσσ hσs
    have hmm : σ.permMatrix K * σ.permMatrix K = 1 := by
      rw [← permMatrix_mul, hσσ, permMatrix_one]
    refine ⟨⟨⟨σ.permMatrix K, σ.permMatrix K, hmm, hmm⟩, ?_⟩, rfl⟩
    rw [mem_unitarySU_iff h]
    refine ⟨?_, ?_⟩
    · change (σ.permMatrix K).det = 1
      rw [det_permutation, hσs]
      simp
    · change ((σ.permMatrix K).map h.bar)ᵀ * σ.permMatrix K = 1
      rw [map_permMatrix, transpose_permMatrix, ← permMatrix_mul, mul_inv_cancel, permMatrix_one]
  obtain ⟨gX, hgX⟩ := hperm σX hXX hsX
  obtain ⟨gY, hgY⟩ := hperm σY hYY hsY
  set S : Finset (Fin 4) := {2, 3}
  have hS : Even S.card := by decide
  set gZ : unitarySU p f K 4 := ⟨sgnGL S, sgnGL_mem_unitarySU h hS⟩
  have hgZ : ((gZ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = sgnMat S := rfl
  have hneg : (-1 : GL (Fin 4) K) ∈ unitarySU p f K 4 := by
    rw [mem_unitarySU_iff h]
    refine ⟨?_, ?_⟩
    · change (-1 : Matrix (Fin 4) (Fin 4) K).det = 1
      rw [det_neg, det_one]
      norm_num
    · change ((-1 : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * (-1 : Matrix (Fin 4) (Fin 4) K) = 1
      rw [Matrix.map_neg _ (map_neg h.bar), Matrix.map_one _ (map_zero h.bar) (map_one h.bar),
        transpose_neg, transpose_one, neg_mul_neg, Matrix.one_mul]
  set gN : unitarySU p f K 4 := ⟨-1, hneg⟩
  set π := unitaryProj h 4
  have hπN : π gN = 1 := by
    change gN ∈ (unitaryProj h 4).ker
    rw [ker_unitaryProj, mem_unitaryScalars]
    refine ⟨-1, ?_, by norm_num, ?_⟩
    · simp [UnitaryFieldData.norm]
    · apply Units.ext
      change (-1 : Matrix (Fin 4) (Fin 4) K) = _
      rw [GeneralLinearGroup.coe_scalar]
      ext i j
      simp only [scalar_apply, diagonal_apply, Matrix.neg_apply, one_apply]
      split_ifs <;> simp
  have hm : ∀ g g' : unitarySU p f K 4, (((g * g' : unitarySU p f K 4) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = (g : GL (Fin 4) K) * (g' : GL (Fin 4) K) := fun _ _ => rfl
  have hext : ∀ g g' : unitarySU p f K 4, ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (g' : GL (Fin 4) K) → g = g' := fun g g' hg => Subtype.ext (Units.ext hg)
  have hX2 : gX * gX = 1 := hext _ _ (by
    rw [hm, hgX, ← permMatrix_mul, hXX, permMatrix_one]; rfl)
  have hY2 : gY * gY = 1 := hext _ _ (by
    rw [hm, hgY, ← permMatrix_mul, hYY, permMatrix_one]; rfl)
  have hZ2 : gZ * gZ = 1 := hext _ _ (by rw [hm, hgZ, sgnMat_mul_self]; rfl)
  have hcXY : gX * gY = gY * gX := hext _ _ (by
    rw [hm, hm, hgX, hgY, ← permMatrix_mul, ← permMatrix_mul, hXY])
  have hdY : (fun i : Fin 4 => if i ∈ S then (-1 : K) else 1) ∘ σY =
      fun i => if i ∈ S then (-1 : K) else 1 := by
    funext i
    fin_cases i <;> simp [S, σY, Equiv.swap_apply_def]
  have hdX : (fun i : Fin 4 => if i ∈ S then (-1 : K) else 1) ∘ σX =
      -fun i => if i ∈ S then (-1 : K) else 1 := by
    funext i
    fin_cases i <;> simp [S, σX, Equiv.swap_apply_def]
  have hcYZ : gY * gZ = gZ * gY := hext _ _ (by
    rw [hm, hm, hgY, hgZ, sgnMat, permMatrix_mul_diagonal, hdY])
  have hcXZ : gX * gZ = gN * (gZ * gX) := hext _ _ (by
    rw [hm, hm, hm, hgX, hgZ, sgnMat, permMatrix_mul_diagonal, hdX]
    change _ = (-1 : Matrix (Fin 4) (Fin 4) K) * _
    rw [neg_one_mul, ← neg_mul, diagonal_neg]
    rfl)
  have hoff : ∀ (g : unitarySU p f K 4) (i j : Fin 4), i ≠ j →
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j ≠ 0 →
        ∀ c : K, ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≠ scalar (Fin 4) c :=
    fun g i j hij hg c => ne_scalar_of_offDiag hij hg c
  have hdg : ∀ (M : Matrix (Fin 4) (Fin 4) K) (i j : Fin 4),
      ((sgnMat S : Matrix (Fin 4) (Fin 4) K) * M) i j = (if i ∈ S then -1 else 1) * M i j :=
    fun M i j => by
    rw [sgnMat, diagonal_mul]
  refine exists_elementary_of_commuting (x := π gX) (y := π gY) (z := π gZ)
    (by rw [← map_mul, hX2, map_one]) (by rw [← map_mul, hY2, map_one])
    (by rw [← map_mul, hZ2, map_one])
    (by change π gX * π gY = π gY * π gX; rw [← map_mul, hcXY, map_mul])
    (by change π gX * π gZ = π gZ * π gX; rw [← map_mul, hcXZ, map_mul, hπN, one_mul, map_mul])
    (by change π gY * π gZ = π gZ * π gY; rw [← map_mul, hcYZ, map_mul]) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact unitaryProj_ne_one h (hoff gX 0 2 (by decide) (by
      rw [hgX, permMatrix_apply]
      simp only [show σX 0 = 2 by decide, ↓reduceIte]
      exact one_ne_zero))
  · exact unitaryProj_ne_one h (hoff gY 0 1 (by decide) (by
      rw [hgY, permMatrix_apply]
      simp only [show σY 0 = 1 by decide, ↓reduceIte]
      exact one_ne_zero))
  · refine unitaryProj_ne_unitaryProj h hY2 (hoff _ 0 3 (by decide) ?_)
    rw [hm, hgX, hgY, ← permMatrix_mul, permMatrix_apply]
    simp only [show (σY * σX) 0 = 3 by decide, ↓reduceIte]
    exact one_ne_zero
  · exact unitaryProj_ne_one h (fun c hc => sgnMat_eq_scalar h2 (hgZ.symm.trans hc)
      (i := 2) (j := 0) (by simp [S]) (by simp [S]))
  · refine unitaryProj_ne_unitaryProj h hX2 (hoff _ 0 2 (by decide) ?_)
    rw [hm, hgZ, hgX, hdg, permMatrix_apply]
    simp only [show (0 : Fin 4) ∉ S by decide, show σX 0 = 2 by decide, ↓reduceIte]
    simp
  · refine unitaryProj_ne_unitaryProj h hY2 (hoff _ 0 1 (by decide) ?_)
    rw [hm, hgZ, hgY, hdg, permMatrix_apply]
    simp only [show (0 : Fin 4) ∉ S by decide, show σY 0 = 1 by decide, ↓reduceIte]
    simp
  · rw [← map_mul]
    have hXY2 : gX * gY * (gX * gY) = 1 := by
      rw [show gX * gY * (gX * gY) = gX * gX * (gY * gY) by
        rw [mul_assoc, ← mul_assoc gY, ← hcXY, mul_assoc, mul_assoc], hX2, hY2, one_mul]
    refine unitaryProj_ne_unitaryProj h hXY2 (hoff _ 0 3 (by decide) ?_)
    rw [hm, hm, hgZ, hgX, hgY, ← permMatrix_mul, hdg, permMatrix_apply]
    simp only [show (0 : Fin 4) ∉ S by decide, show (σY * σX) 0 = 3 by decide, ↓reduceIte]
    simp

include h in
theorem exists_elementary_unitaryPSU (hp2 : p ≠ 2) {n : ℕ} (hn : 4 ≤ n) :
    ∃ E : Subgroup (unitaryPSU h n), IsElementaryAbelian 2 E ∧ 4 < Nat.card E := by
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5
  · exact exists_elementary_unitaryPSU_four h hp2
  · exact exists_elementary_unitaryPSU_five h hp2 h5

end UnitaryEight

theorem prime_cube_dvd_card_psu {K : Type} [Field K] {p g n : ℕ} (hp : p.Prime) (hg : 1 ≤ g)
    (hK : Nat.card K = (p ^ g) ^ 2) (hn : 3 ≤ n) :
    p ^ 3 ∣ Nat.card (StatedProj (StatedSU n (p ^ g) K)) := by
  rw [Timmesfeld.ClassicalOrders.card_statedProj_statedSU hp hg hK (by omega)]
  set q := p ^ g with hq
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ hp.pos
  set P := ∏ i ∈ Finset.Icc 2 n, (((q : ℕ) : ℤ) ^ i - (-1) ^ i).toNat with hP
  set d := Nat.gcd n (q + 1) with hd
  have hterm : (((q : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat = (q + 1) * (q - 1) := by
    have h0 : (0 : ℤ) ≤ ((q : ℕ) : ℤ) ^ 2 - (-1) ^ 2 := by
      have : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq1
      nlinarith
    apply Int.ofNat.inj
    rw [Int.ofNat_eq_natCast, Int.toNat_of_nonneg h0, Int.ofNat_eq_natCast, Nat.cast_mul,
      Nat.cast_sub hq1]
    push_cast
    ring
  have hdP : d ∣ P := by
    have h2 : (2 : ℕ) ∈ Finset.Icc 2 n := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    refine (Nat.gcd_dvd_right n (q + 1)).trans ?_
    refine (dvd_mul_right (q + 1) (q - 1)).trans ?_
    rw [← hterm]
    exact Finset.dvd_prod_of_mem _ h2
  have hdvd : d ∣ q ^ (n * (n - 1) / 2) * P := dvd_mul_of_dvd_right hdP _
  have hcop : Nat.Coprime (p ^ 3) d := by
    refine Nat.Coprime.pow_left 3 (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right n (q + 1)) ?_)
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hpd
    have h1 : p ∣ 1 := (Nat.dvd_add_right (dvd_pow_self p (by omega : g ≠ 0))).mp hpd
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one h1)
  have hpow : p ^ 3 ∣ q ^ (n * (n - 1) / 2) := by
    rw [hq, ← pow_mul]
    refine pow_dvd_pow p ?_
    have h3 : 3 ≤ n * (n - 1) / 2 := by
      have h6 : 6 ≤ n * (n - 1) := Nat.mul_le_mul hn (show 2 ≤ n - 1 by omega)
      omega
    exact h3.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hmul : q ^ (n * (n - 1) / 2) * P / d * d = q ^ (n * (n - 1) / 2) * P :=
    Nat.div_mul_cancel hdvd
  exact hcop.dvd_of_dvd_mul_right (by rw [hmul]; exact dvd_mul_of_dvd_left hpow _)

variable {A : Type} [Group A] {a : A} {L : Subgroup A}

theorem graph_field_case_false (ha : orderOf a = 2) {m ℓ e : ℕ} (hm : 4 ≤ m) (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) {k : Type} [Field k] (hk : Nat.card k = ℓ ^ e)
    {ρ : A →* MulAut (projectiveSL m k)} (hinj : Function.Injective ρ)
    (hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      (OuterAutomorphisms.inner (projectiveSL m k) ⊓ centralizer {ρ a}))
    {B : GL (Fin m) k} {σ : k ≃+* k} (hσ : σ ≠ 1)
    (hρa : ρ a = conjAut m k B * fieldAut m k σ * dualAut m k) {p f : ℕ} (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2) : False := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ hℓ.ne_zero)
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hα2 : (conjAut m k B * fieldAut m k σ * dualAut m k) ^ 2 = 1 := by
    rw [← hρa, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  obtain ⟨heven, hσx, H, hH⟩ :=
    UnitaryHigher.linear_graph_field_involution_descent hℓ he hk (by omega) B σ hσ hα2
  have hg : 1 ≤ e / 2 := by obtain ⟨r, hr⟩ := heven; omega
  have hKe : Nat.card k = ℓ ^ (2 * (e / 2)) := by
    rw [hk]
    congr 1
    obtain ⟨r, hr⟩ := heven
    omega
  have hud : UnitaryFieldData ℓ (e / 2) k := ⟨hℓ, hg, hKe⟩
  have hσbar : ∀ x, σ x = hud.bar x := fun x => by rw [hσx, hud.bar_apply]
  obtain ⟨-, ⟨ι, -⟩, hNinn, -, hNC, hNnormal, hCN⟩ :=
    linear_graph_field_full_centralizer_rigidity hud (n := m) (by omega) σ hσbar
  set χ := conjAut m k H with hχ
  set β := fieldAut m k σ * dualAut m k with hβ
  set N := (unitarySU ℓ (e / 2) k m).map (conjAut m k) with hNdef
  have hρa' : ρ a = χ * β * χ⁻¹ := by rw [hρa, hH]
  have hY : (OuterAutomorphisms.inner (projectiveSL m k) ⊓ centralizer {ρ a}).map
      (MulAut.conj χ⁻¹).toMonoidHom =
        OuterAutomorphisms.inner (projectiveSL m k) ⊓ centralizer {β} := by
    rw [map_conj_inner_inf_centralizer, hρa']
    congr 3
    group
  set L₀ := (L.map ρ).map (MulAut.conj χ⁻¹).toMonoidHom with hL₀def
  have hL₀ : CFSG.Assembly.IsComponentOf L₀
      (OuterAutomorphisms.inner (projectiveSL m k) ⊓ centralizer {β}) := by
    have := isComponentOf_map_conj hL₁ χ⁻¹
    rwa [hY] at this
  have := finite_mulAut_projectiveSL (k := k) m
  have hL₀N : CFSG.Assembly.IsComponentOf L₀ N := by
    refine isComponentOf_of_normal_of_comm (le_inf hNinn hNC)
      (fun y hy => mem_normalizer_of_normal_subgroupOf hNC hNnormal hy.2) ?_ hL₀
    intro x _ hx y _ hy
    rw [hCN] at hx hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow_self β i j).eq
  have hK2 : Nat.card k = (ℓ ^ (e / 2)) ^ 2 := by rw [hKe, ← pow_mul, mul_comm]
  have eU : unitaryPSU hud m ≃* StatedProj (StatedSU m (ℓ ^ (e / 2)) k) :=
    unitaryPSUEquiv hud (by omega)
  have hnq : (m, ℓ ^ (e / 2)) ≠ (3, 2) := fun h => by
    have := congrArg Prod.fst h
    simp only at this
    omega
  have : IsSimpleGroup (StatedProj (StatedSU m (ℓ ^ (e / 2)) k)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU k ℓ (e / 2) hK2 m
      (by omega) hnq
  have : IsSimpleGroup (unitaryPSU hud m) := eU.isSimpleGroup
  have hNs : IsSimpleGroup N := ι.symm.isSimpleGroup
  have hL₀eq : L₀ = N := eq_of_isComponentOf_simple hNs hL₀N
  have hLimg : L.map ρ = N.map (MulAut.conj χ).toMonoidHom := by
    rw [← hL₀eq, hL₀def, map_conj_inv_map_conj]
  have eL : L ≃* unitaryPSU hud m :=
    ((L.equivMapOfInjective ρ hinj).trans ((MulEquiv.subgroupCongr hLimg).trans
      ((N.equivMapOfInjective _ (MulAut.conj χ).injective).symm))).trans ι.symm
  have hLnab : ∃ x y : L, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := exists_ne_commute_of_isQuasisimple hL₁.2.2
    set eρ := L.equivMapOfInjective ρ hinj
    refine ⟨eρ.symm x, eρ.symm y, fun hc => hxy ?_⟩
    have := congrArg eρ hc
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  have : IsSimpleGroup L := eL.isSimpleGroup
  have eZ : L ⧸ center L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_isSimpleGroup hLnab)).trans
      QuotientGroup.quotientBot
  obtain ⟨E, hE, hEcard⟩ := exists_elementary_unitaryPSU hud hℓ2 hm
  have hdvd : ℓ ^ 3 ∣ Nat.card (unitaryPSU hud m) := by
    rw [Nat.card_congr eU.toEquiv]
    exact prime_cube_dvd_card_psu hℓ hg hK2 (by omega)
  exact false_of_not_small_source
    (not_small_source_of_mulEquiv (eZ.trans eL) E hEcard hℓ hℓ2 hdvd) hp2 hsrc

end CFSG.ComponentClassification.OddSelector
