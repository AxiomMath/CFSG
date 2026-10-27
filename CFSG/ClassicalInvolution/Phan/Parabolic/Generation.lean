module

public import CFSG.ClassicalInvolution.Phan.Defs

public section

namespace CFSG.ClassicalInvolution.Phan

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg

section Su2

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem exists_smul_snd_eq_zero (hσ : IsUnitaryInvolution σ) {w : Fin 2 → K}
    (hw : herm σ w w ≠ 0) : ∃ A : SUid σ 2, (A • w) 1 = 0 := by
  obtain ⟨l, hl⟩ := exists_smul_norm_one hσ hw
  have hl' : σ l * l * herm σ w w = 1 := by
    rw [herm_smul_left, herm_smul_right, ← mul_assoc] at hl
    exact hl
  have hν' : σ (w 0) * w 0 + σ (w 1) * w 1 = herm σ w w := by
    simp [herm, Fin.sum_univ_two]
  generalize herm σ w w = ν at hl' hν'
  let A : Matrix (Fin 2) (Fin 2) K := !![σ l * σ (w 0), σ l * σ (w 1); -(l * w 1), l * w 0]
  have hdet : A.det = 1 := by
    rw [Matrix.det_fin_two]
    simp only [A, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val_zero]
    linear_combination (σ l * l) * hν' + hl'
  have hconj : conjTr σ A * A = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two, A, map_mul, hσ.invol]
    · linear_combination (σ l * l) * hν' + hl'
    · ring
    · ring
    · linear_combination (σ l * l) * hν' + hl'
  refine ⟨mkSU σ A hdet fun x y => by rw [herm_mulVec, hconj, one_mulVec], ?_⟩
  simp [mkSU_smul, A, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

end Su2

section Transvections

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem tvMat_eq_embPair_two (a : Fin 3 → K) (c : K) (h2 : a 2 = 0) :
    tvMat σ a c = embPair 2 (tvMat σ ![a 0, a 1] c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tvMat, embPair, Matrix.vecMulVec_apply, h2, -Matrix.cons_vecMulVec]

theorem tvMat_eq_embPair_zero (a : Fin 3 → K) (c : K) (h0 : a 0 = 0) :
    tvMat σ a c = embPair 0 (tvMat σ ![a 1, a 2] c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tvMat, embPair, Matrix.vecMulVec_apply, h0, -Matrix.cons_vecMulVec]

theorem mem_range_embSUid_two_of_tv (hσ : IsUnitaryInvolution σ) {g : SUid σ 3} {a : Fin 3 → K}
    {c : K} (ha : herm σ a a = 0) (hc : c + σ c = 0)
    (hg : ∀ v, g • v = v + (c * herm σ a v) • a) (h2 : a 2 = 0) :
    g ∈ (embSUid σ 2).range := by
  have ha' : herm σ ![a 0, a 1] ![a 0, a 1] = 0 := by
    simpa [herm, Fin.sum_univ_three, Fin.sum_univ_two, h2] using ha
  refine ⟨tv hσ.invol ha' hc, ext_smul σ fun v => ?_⟩
  rw [hg v, smul_def, coe_embSUid]
  show embPair 2 (tvMat σ ![a 0, a 1] c) *ᵥ v = _
  rw [← tvMat_eq_embPair_two a c h2, tvMat_mulVec]

theorem mem_range_embSUid_zero_of_tv (hσ : IsUnitaryInvolution σ) {g : SUid σ 3} {a : Fin 3 → K}
    {c : K} (ha : herm σ a a = 0) (hc : c + σ c = 0)
    (hg : ∀ v, g • v = v + (c * herm σ a v) • a) (h0 : a 0 = 0) :
    g ∈ (embSUid σ 0).range := by
  have ha' : herm σ ![a 1, a 2] ![a 1, a 2] = 0 := by
    simpa [herm, Fin.sum_univ_three, Fin.sum_univ_two, h0] using ha
  refine ⟨tv hσ.invol ha' hc, ext_smul σ fun v => ?_⟩
  rw [hg v, smul_def, coe_embSUid]
  show embPair 0 (tvMat σ ![a 1, a 2] c) *ᵥ v = _
  rw [← tvMat_eq_embPair_zero a c h0, tvMat_mulVec]

end Transvections

section Generation

theorem embSUid_sup_eq_top {K : Type} [Field K] {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ)
    (h3 : ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1) :
    (embSUid σ 2).range ⊔ (embSUid σ 0).range = ⊤ := by
  rw [eq_top_iff, ← T_eq_top hσ (by norm_num) (fun _ => h3), T, Subgroup.closure_le]
  rintro g ⟨a, c, ha, hc, hg⟩
  by_cases h2 : a 2 = 0
  · exact Subgroup.mem_sup_left (mem_range_embSUid_two_of_tv hσ ha hc hg h2)
  by_cases h0 : a 0 = 0
  · exact Subgroup.mem_sup_right (mem_range_embSUid_zero_of_tv hσ ha hc hg h0)
  have hν : herm σ ![a 1, a 2] ![a 1, a 2] ≠ 0 := by
    intro h
    apply h0
    have h1 : σ (a 0) * a 0 = 0 := by
      simp only [herm, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one] at ha h
      linear_combination ha - h
    rcases mul_eq_zero.1 h1 with h' | h'
    · simpa using (map_eq_zero_iff σ σ.injective).1 h'
    · exact h'
  obtain ⟨A, hA⟩ := exists_smul_snd_eq_zero hσ hν
  have hA' : ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 * a 1 +
      ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 * a 2 = 0 := by
    have := hA
    simpa [smul_def, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hh2 : (embSUid σ 0 A • a) 2 = 0 := by
    simp only [smul_def, coe_embSUid, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    simpa [embPair] using hA'
  have hha : herm σ (embSUid σ 0 A • a) (embSUid σ 0 A • a) = 0 := by
    rw [herm_smul_smul, ha]
  have htv : ∀ v, tv hσ.invol hha hc • v =
      v + (c * herm σ (embSUid σ 0 A • a) v) • (embSUid σ 0 A • a) := tv_smul hσ.invol hha hc
  have htB := mem_range_embSUid_two_of_tv hσ hha hc htv hh2
  have hg' : g = (embSUid σ 0 A)⁻¹ * tv hσ.invol hha hc * ((embSUid σ 0 A)⁻¹)⁻¹ := by
    refine ext_smul σ fun v => ?_
    rw [hg v, conj_smul_of_tv (embSUid σ 0 A)⁻¹ _ htv v, inv_smul_smul]
  have hhB : embSUid σ 0 A ∈ (embSUid σ 2).range ⊔ (embSUid σ 0).range :=
    Subgroup.mem_sup_right ⟨A, rfl⟩
  rw [hg']
  exact mul_mem (mul_mem (inv_mem hhB) (Subgroup.mem_sup_left htB)) (by rw [inv_inv]; exact hhB)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem B12_sup_B23_eq_top (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) :
    B12 K p f ⊔ B23 K p f = ⊤ :=
  embSUid_sup_eq_top (isUnitaryInvolution_unitaryInvolution hK) (exists_norm_ne_one hK hq)

end Generation

end CFSG.ClassicalInvolution.Phan
