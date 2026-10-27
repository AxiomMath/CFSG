module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ModelBridge
public import CFSG.Open.StatedDefs
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open Matrix Equiv Equiv.Perm

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

noncomputable def colUnit (a : ι) (v : ι → K) (h : v a ≠ 0) : GL ι K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.updateCol (1 : Matrix ι ι K) a v) (by
    have := det_updateCol_sum (1 : Matrix ι ι K) a v
    have e : (fun k => ∑ i, v i • (1 : Matrix ι ι K) k i) = v := by
      funext k; simp [Matrix.one_apply]
    rw [e] at this
    simpa [this] using h)

theorem colUnit_mulVec (a : ι) (v : ι → K) (h : v a ≠ 0) :
    (colUnit a v h : Matrix ι ι K) *ᵥ Pi.single a 1 = v := by
  rw [colUnit]
  simp only [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  funext i
  rw [Matrix.mulVec_single_one]
  simp [Matrix.col_apply]

@[expose] noncomputable def permGL (σ : Perm ι) : GL ι K :=
  (Matrix.permMatrixHom : Perm ι →* Matrix ι ι K).toHomUnits σ

theorem permGL_val (σ : Perm ι) : ((permGL σ : GL ι K) : Matrix ι ι K) = σ⁻¹.permMatrix K := rfl

theorem permGL_injective : Function.Injective (permGL : Perm ι → GL ι K) := by
  intro σ τ h
  have h' := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) h
  simp only [permGL_val] at h'
  have := PEquiv.toMatrix_injective h'
  have h2 : σ⁻¹ = τ⁻¹ := by
    ext x
    have := congrArg (fun p => p x) this
    simpa [Equiv.toPEquiv_apply] using this
  simpa using h2

theorem permGL_mulVec (σ : Perm ι) (v : ι → K) :
    ((permGL σ : GL ι K) : Matrix ι ι K) *ᵥ v = v ∘ ⇑σ⁻¹ := by
  rw [permGL_val, permMatrix_mulVec]

theorem permGL_det_of_isThreeCycle {σ : Perm ι} (h : σ.IsThreeCycle) :
    ((permGL σ : GL ι K) : Matrix ι ι K).det = 1 := by
  rw [permGL_val, det_permutation, h.inv.sign]
  simp

theorem orderOf_permGL {σ : Perm ι} (h : σ.IsThreeCycle) : orderOf (permGL σ : GL ι K) = 3 := by
  have := orderOf_injective (Matrix.permMatrixHom : Perm ι →* Matrix ι ι K).toHomUnits
    (fun x y hxy => permGL_injective hxy) σ
  exact this.trans h.orderOf

theorem exists_det_one_orderOf_three_smul (hι : 3 ≤ Fintype.card ι) (v : ι → K) :
    ∃ g : GL ι K, orderOf g = 3 ∧ (g : Matrix ι ι K).det = 1 ∧ g • v = v := by
  classical
  by_cases hv : v = 0
  · obtain ⟨a, -, j, -, k, -, haj, hak, hjk⟩ := Finset.two_lt_card.mp
      (show 2 < (Finset.univ : Finset ι).card by rw [Finset.card_univ]; omega)
    have h3 := isThreeCycle_swap_mul_swap_same haj hak hjk
    exact ⟨permGL (swap a j * swap a k), orderOf_permGL h3, permGL_det_of_isThreeCycle h3, by
      subst hv; exact smul_zero _⟩
  · obtain ⟨a, ha⟩ := Function.ne_iff.mp hv
    have hcard : 1 < (Finset.univ.erase a).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ a)]; simp only [Finset.card_univ]; omega
    obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp hcard
    have haj : a ≠ j := (Finset.ne_of_mem_erase hj).symm
    have hak : a ≠ k := (Finset.ne_of_mem_erase hk).symm
    have h3 := isThreeCycle_swap_mul_swap_same haj hak hjk
    set σ : Perm ι := swap a j * swap a k with hσ
    set u : ι → K := fun x => if x = a ∨ x = j ∨ x = k then 1 else 0 with hu
    have hua : u a ≠ 0 := by simp [hu]
    have hmem : ∀ x, (σ⁻¹ x = a ∨ σ⁻¹ x = j ∨ σ⁻¹ x = k) ↔ (x = a ∨ x = j ∨ x = k) := by
      intro x
      simp only [hσ, _root_.mul_inv_rev, swap_inv, Perm.mul_apply, swap_apply_def]
      split_ifs <;> simp_all
    have hfix : ((permGL σ : GL ι K) : Matrix ι ι K) *ᵥ u = u := by
      rw [permGL_mulVec]
      funext x
      simp only [Function.comp_apply, hu]
      exact if_congr (hmem x) rfl rfl
    set Bv := colUnit a v ha with hBv
    set Bu := colUnit a u hua with hBu
    set C : GL ι K := Bv * Bu⁻¹ with hC
    have hBu' : ((Bu⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ u = Pi.single a 1 := by
      rw [← colUnit_mulVec a u hua, mulVec_mulVec]
      simp only [hBu, Units.inv_mul, one_mulVec]
    have hCu : C • u = v := by
      change ((C : GL ι K) : Matrix ι ι K) *ᵥ u = v
      rw [hC, Units.val_mul, ← mulVec_mulVec, hBu']
      exact colUnit_mulVec a v ha
    have hPu : (permGL σ : GL ι K) • u = u := by
      change ((permGL σ : GL ι K) : Matrix ι ι K) *ᵥ u = u
      exact hfix
    refine ⟨C * (permGL σ : GL ι K) * C⁻¹, ?_, ?_, ?_⟩
    · have := orderOf_injective (MulAut.conj C).toMonoidHom (MulAut.conj C).injective (permGL σ : GL ι K)
      rw [orderOf_permGL h3] at this
      simpa [MulAut.conj_apply] using this
    · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, permGL_det_of_isThreeCycle h3, mul_one,
        ← det_mul]
      simp
    · rw [← hCu, mul_smul, mul_smul, inv_smul_smul, hPu]

theorem threeFixedModel_of_detOne (hι : 3 ≤ Fintype.card ι) (Γ : Subgroup (GL ι K))
    (hΓ : ∀ A : GL ι K, (A : Matrix ι ι K).det = 1 → A ∈ Γ) :
    ThreeFixedModel Γ (ι → K) := by
  intro v
  obtain ⟨g, hg3, hdet, hgv⟩ := exists_det_one_orderOf_three_smul hι v
  exact ⟨⟨g, hΓ g hdet⟩, by rw [Subgroup.orderOf_mk]; exact hg3, hgv⟩

theorem threeFixedModel_statedSL {K : Type} [Field K] {n : ℕ} (hn : 3 ≤ n) :
    ThreeFixedModel (CFSG.Open.StatedSL n K) (Fin n → K) :=
  threeFixedModel_of_detOne (by simpa using hn) _ fun _ hA => Subgroup.subset_closure hA

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
