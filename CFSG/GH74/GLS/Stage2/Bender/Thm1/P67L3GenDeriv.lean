module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67L3Gen

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

section Deriv

variable {K : Type} [Field K]

theorem rootElt_add (B : GL (Fin 3) K) {i j : Fin 3} (hij : i ≠ j) (s t : K) :
    rootElt B hij (s + t) = rootElt B hij s * rootElt B hij t := by
  rw [rootElt_def, rootElt_def, rootElt_def, SpecialLinearGroup.transvection_add, map_mul, map_mul]

theorem conjAut_diagGLK_proj_diag (d : Fin 3 → K) (hd : ∀ k, d k ≠ 0)
    (S : SpecialLinearGroup (Fin 3) K) (e : Fin 3 → K)
    (hS : (S : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal e) :
    conjAut 3 K (diagGLK d hd) (proj 3 K S) = proj 3 K S := by
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix,
    Units.mul_inv_eq_iff_eq_mul]
  show ((diagGLK d hd : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * _ = _ *
    ((diagGLK d hd : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  rw [coe_diagGLK, hS, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext l
  exact mul_comm _ _

theorem exists_third (i j : Fin 3) (hij : i ≠ j) : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
  revert i j; decide

theorem rootElt_mem_derived {B : GL (Fin 3) K} {w : MulAut (projectiveSL 3 K)}
    (hw : ∃ (x : GL (Fin 3) K) (d : Fin 3 → K), w = conjAut 3 K x ∧
      (x : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) =
        (B : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal d)
    {i j : Fin 3} (hij : i ≠ j) (hfix : ∀ t, w (rootElt B hij t) = rootElt B hij t)
    {g : K} (hg0 : g ≠ 0) (hg1 : g ≠ 1) (t : K) :
    rootElt B hij t ∈ ⁅fixSub w, fixSub w⁆ := by
  obtain ⟨k, hik, hjk⟩ := exists_third i j hij
  set S : SpecialLinearGroup (Fin 3) K := SpecialLinearGroup.diag2n hik g hg0 with hSdef
  set dd : Fin 3 → K := fun l => if l = i then g else if l = k then g⁻¹ else 1 with hddef
  have hSd : (S : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal dd := SpecialLinearGroup.diag2n_coe hik g hg0
  have hdd0 : ∀ l, dd l ≠ 0 := by
    intro l
    simp only [hddef]
    split_ifs <;> simp [hg0]
  have hddi : dd i = g := by simp [hddef]
  have hddj : dd j = 1 := by simp [hddef, hij.symm, hjk]
  set tor : projectiveSL 3 K := conjAut 3 K B (proj 3 K S) with htor
  have hwtor : w tor = tor := by
    obtain ⟨x, d, rfl, hxd⟩ := hw
    have hd := diag_ne_zero_of_mul_eq hxd
    have hGL : x * B = B * diagGLK d hd := Units.ext (by
      rw [Units.val_mul, Units.val_mul, coe_diagGLK]; exact hxd)
    show conjAut 3 K x (conjAut 3 K B (proj 3 K S)) = conjAut 3 K B (proj 3 K S)
    rw [← MulAut.mul_apply, ← map_mul, hGL, map_mul, MulAut.mul_apply,
      conjAut_diagGLK_proj_diag d hd S dd hSd]
  have hconj : ∀ s : K, tor * rootElt B hij s * tor⁻¹ = rootElt B hij (g * s) := by
    intro s
    have h1 : MulAut.conj (proj 3 K S) = conjAut 3 K (diagGLK dd hdd0) := by
      rw [← conjAut_toGL]
      congr 1
      apply Units.ext
      rw [coe_diagGLK]
      exact hSd
    have h2 : tor * rootElt B hij s * tor⁻¹ =
        conjAut 3 K B (MulAut.conj (proj 3 K S) (proj 3 K (SpecialLinearGroup.transvection hij s))) := by
      simp [htor, rootElt_def, MulAut.conj_apply, map_mul, map_inv]
    rw [h2, h1, conjAut_diagGLK_proj_transvection hij dd hdd0 s, hddi, hddj, div_one, rootElt_def]
  have hcomm : ∀ s : K, ⁅tor, rootElt B hij s⁆ = rootElt B hij ((g - 1) * s) := by
    intro s
    rw [commutatorElement_def, hconj, sub_mul, one_mul]
    have : rootElt B hij (g * s) = rootElt B hij (g * s - s) * rootElt B hij s := by
      rw [← rootElt_add, sub_add_cancel]
    rw [this]
    group
  have hg1' : g - 1 ≠ 0 := sub_ne_zero.mpr hg1
  have : rootElt B hij t = ⁅tor, rootElt B hij (t / (g - 1))⁆ := by
    rw [hcomm, mul_div_cancel₀ _ hg1']
  rw [this]
  exact Subgroup.commutator_mem_commutator (mem_fixSub.2 hwtor) (mem_fixSub.2 (hfix _))

end Deriv

section Main

variable {K : Type} [Field K] [Finite K]

theorem generation_of_toral_deriv {r : ℕ} (hr : 1 < r)
    {V : Subgroup (MulAut (projectiveSL 3 K))} (hVc : Nat.card V = r ^ 2)
    (hVe : ∀ v ∈ V, v ^ r = 1) (B : GL (Fin 3) K)
    (hV : ∀ v ∈ V, ∃ (x : GL (Fin 3) K) (d : Fin 3 → K), v = conjAut 3 K x ∧
      (x : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) =
        (B : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal d) {g : K} (hg0 : g ≠ 0) (hg1 : g ≠ 1) :
    (⨆ v ∈ V, ⨆ (_ : v ≠ 1), ⁅fixSub v, fixSub v⁆) = ⊤ := by
  apply eq_top_of_rootElt_mem B
  intro i j hij t
  obtain ⟨w, hwV, hw1, hwt⟩ := exists_ne_one_fix_rootElt hr hVc hVe B hV hij
  have hle : ⁅fixSub w, fixSub w⁆ ≤ ⨆ v ∈ V, ⨆ (_ : v ≠ 1), ⁅fixSub v, fixSub v⁆ :=
    le_iSup₂_of_le w hwV (le_iSup (fun _ : w ≠ 1 => ⁅fixSub w, fixSub w⁆) hw1)
  exact hle (rootElt_mem_derived (hV w hwV) hij hwt hg0 hg1 t)

theorem false_of_toral_deriv {r : ℕ} {V Z : Subgroup (MulAut (projectiveSL 3 K))}
    (h2 : N2Cfg (projectiveSL 3 K) r V Z) (h3 : N3Deriv (projectiveSL 3 K) V Z)
    (h2K : (2 : K) ≠ 0) (B : GL (Fin 3) K)
    (hV : ∀ v ∈ V, ∃ (x : GL (Fin 3) K) (d : Fin 3 → K), v = conjAut 3 K x ∧
      (x : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) =
        (B : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal d) : False := by
  have h2' := h2
  obtain ⟨hr, -, hVe, hVc, -⟩ := h2'
  have : IsElementaryAbelian r ↥V := hVe
  have hVe' : ∀ v ∈ V, v ^ r = 1 := fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv
  have hg0 : (-1 : K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hg1 : (-1 : K) ≠ 1 := by
    intro h
    apply h2K
    have h' : (1 : K) + 1 = 0 := by
      calc (1 : K) + 1 = -1 + 1 := by rw [h]
        _ = 0 := by simp
    rwa [one_add_one_eq_two] at h'
  exact false_of_generation_deriv isSimpleGroup_projectiveSL_three exists_noncomm_projectiveSL_three h2 h3
    (generation_of_toral_deriv hr.one_lt hVc hVe' B hV hg0 hg1)

end Main

end CFSG.GH74.GLS.Stage2.Bender.Thm1
