module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269Six2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I269Six

open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary mem_primeFormUnitary)
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo (hF4 bar hF4_bar)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.Fischer
open scoped commutatorElement

theorem commute_diag_of_block {M : Matrix (Fin 6) (Fin 6) F4} {d δ : Fin 6 → F4}
    (hM : M * Matrix.diagonal d = Matrix.diagonal d * M) (hδ : ∀ i j, d i = d j → δ i = δ j) :
    M * Matrix.diagonal δ = Matrix.diagonal δ * M := by
  ext i j
  by_cases hM0 : M i j = 0
  · simp [Matrix.mul_diagonal, Matrix.diagonal_mul, hM0]
  · have hd : d i = d j := by
      by_contra hne
      exact hM0 (zero_of_commute_diag hM hne)
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hδ i j hd, mul_comm]

@[expose] def dGL (δ : Fin 6 → F4) (hδ : ∀ i, δ i ≠ 0) : GL (Fin 6) F4 :=
  { val := Matrix.diagonal δ
    inv := Matrix.diagonal (fun i => (δ i)⁻¹)
    val_inv := by
      rw [Matrix.diagonal_mul_diagonal]
      simp [mul_inv_cancel₀ (hδ _)]
    inv_val := by
      rw [Matrix.diagonal_mul_diagonal]
      simp [inv_mul_cancel₀ (hδ _)] }

theorem dGL_val (δ : Fin 6 → F4) (hδ : ∀ i, δ i ≠ 0) :
    ((dGL δ hδ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal δ := rfl

theorem dGL_mem_UG (δ : Fin 6 → F4) (hδ : ∀ i, δ i ≠ 0) (h3 : ∀ i, δ i ^ 3 = 1) :
    dGL δ hδ ∈ primeFormUnitary hF4 (idGram F4 6) := by
  rw [mem_primeFormUnitary]
  have hid : idGram F4 6 = 1 := by ext i j; simp [idGram, Matrix.one_apply]
  rw [hid, dGL_val]
  ext i j
  by_cases hij : i = j
  · subst hij
    have e : bar (δ i) * δ i = 1 := by
      rw [show bar (δ i) = δ i ^ 2 by simp [bar, frobenius_def], ← pow_succ]
      exact h3 i
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply, hF4_bar, e]
  · simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply, hij]

theorem commute_D {Ê : Subgroup M6} {d : Fin 6 → F4}
    (hcomm : ∀ h ∈ Ê, ∀ k ∈ Ê, ⁅h, k⁆ ∈ Zs) {D : M6} (hDd : mM6 D = Matrix.diagonal d)
    (hDÊ : D ∈ Ê) (htr : (Matrix.diagonal d).trace ≠ 0) :
    ∀ h ∈ Ê, mM6 h * Matrix.diagonal d = Matrix.diagonal d * mM6 h := by
  intro h hh
  obtain ⟨c, hc⟩ := mem_Zs.1 (hcomm h hh D hDÊ)
  have hc' : (h : GL (Fin 6) F4) * (D : GL (Fin 6) F4) * ((h : GL (Fin 6) F4))⁻¹ *
      (D : GL (Fin 6) F4)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
    rw [← hc]; simp [commutatorElement_def]
  have h2 : (h : GL (Fin 6) F4) * (D : GL (Fin 6) F4) * (h : GL (Fin 6) F4)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 6) c * (D : GL (Fin 6) F4) := by
    rw [← hc']; group
  have h3 := congrArg (fun g : GL (Fin 6) F4 => (g : Matrix (Fin 6) (Fin 6) F4)) h2
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h3
  have hA : ((h : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) * Matrix.diagonal d *
      (((h : GL (Fin 6) F4))⁻¹ : GL (Fin 6) F4) = (c : F4) • Matrix.diagonal d := by
    rw [← hDd, Matrix.smul_eq_diagonal_mul]
    simpa [hDd] using h3
  exact commute_of_conj_smul (h : GL (Fin 6) F4) (Matrix.diagonal d) (c : F4) htr hA



open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.Fischer

theorem cube_one {Ê : Subgroup M6} {d : Fin 6 → F4} {l : F4} {i1 i2 : Fin 6}
    (hcube : ∀ h ∈ Ê, h ^ 3 ∈ Zs)
    (hblock : ∀ h ∈ Ê, ∀ i j, d i ≠ d j → mM6 h i j = 0)
    (hd1 : ∀ j, j ≠ i1 → d j ≠ d i1) :
    ∀ h ∈ Ê, (h : GL (Fin 6) F4) ^ 3 = 1 ∧ mM6 h i1 i1 ^ 3 = 1 := by
  intro h hh
  have hblk : ∀ j, j ≠ i1 → mM6 h i1 j = 0 ∧ mM6 h j i1 = 0 := fun j hj =>
    ⟨hblock h hh i1 j (hd1 j hj).symm, hblock h hh j i1 (hd1 j hj)⟩
  have hc3 := cube_entry (mM6 h) i1 hblk
  obtain ⟨c, hc⟩ := mem_Zs.1 (hcube h hh)
  have hM : (((h ^ 3 : M6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      Matrix.scalar (Fin 6) (c : F4) := by
    rw [hc]; simp [Matrix.GeneralLinearGroup.coe_scalar]
  have hM' : (((h ^ 3 : M6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = mM6 h * mM6 h * mM6 h := by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, pow_three, mul_assoc]
  have ha : mM6 h i1 i1 ^ 3 = (c : F4) := by
    rw [← hc3, ← hM', hM, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
  have hc0 : (c : F4) ≠ 0 := Units.ne_zero c
  have ha0 : mM6 h i1 i1 ≠ 0 := by
    intro h0; apply hc0; rw [← ha, h0]; ring
  have hc1 : (c : F4) = 1 := by rw [← ha, f4_cube _ ha0]
  refine ⟨?_, by rw [ha, hc1]⟩
  rw [← Subgroup.coe_pow, hc]
  have : c = 1 := Units.ext hc1
  rw [this]
  exact map_one _

end CFSG.LocalAnalysis.GLTheoremA.I269Six

end
