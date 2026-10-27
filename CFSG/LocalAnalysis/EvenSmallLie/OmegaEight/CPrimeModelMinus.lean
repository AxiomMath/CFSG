module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CPrimeModelPerm

public section

namespace CFSG.EvenSmallLie.OmegaEight.CPrimeModel

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Stage1.Model

theorem minus_parts : memL .minus OmegaEightMinus.genArrs[10]! = false ∧
    eqA 136 (compA 136 OmegaEightMinus.genArrs[10]! OmegaEightMinus.genArrs[10]!) (idA 136) =
      true := by
  have h := minusCheck_ok
  simp only [minusCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h

theorem gen10_not_mem : OmegaEightMinus.gen 10 ∉ OmegaEightMinus.omegaT := by
  intro h
  have h1 := (memL_iff (ε := .minus) (OmegaEightMinus.rep_gen (by norm_num : 10 < 11))).2 h
  rw [minus_parts.1] at h1
  exact absurd h1 (by decide)

theorem gen10_mul_self : OmegaEightMinus.gen 10 * OmegaEightMinus.gen 10 = 1 :=
  eq_of_eqA (rep_compA (OmegaEightMinus.rep_gen (by norm_num))
    (OmegaEightMinus.rep_gen (by norm_num))) rep_idA minus_parts.2

theorem inv_mul_gen10_mem {g : Equiv.Perm (Fin 136)} (hgA : g ∈ OmegaEightMinus.autT)
    (hg : g ∉ OmegaEightMinus.omegaT) :
    g⁻¹ * OmegaEightMinus.gen 10 ∈ OmegaEightMinus.omegaT := by
  have h10 := OmegaEightMinus.gen_mem_autT (by norm_num : 10 < 11)
  obtain ⟨j, hj⟩ := exists_coset_rep (H := OmegaEightMinus.omegaT) (K := OmegaEightMinus.autT)
    (m := 2) (fun j => OmegaEightMinus.gen 10 ^ (j : ℕ)) (fun j => pow_mem h10 _)
    OmegaEightMinus.omegaT_le_autT
    OmegaEightMinus.card_autT_eq (fun i j h => by
      fin_cases i <;> fin_cases j
      · rfl
      · exfalso
        apply gen10_not_mem
        simpa using h
      · exfalso
        apply gen10_not_mem
        simpa using h
      · rfl) hgA
  fin_cases j
  · exact absurd (by simpa using hj) hg
  · have hj' : g * (OmegaEightMinus.gen 10)⁻¹ ∈ OmegaEightMinus.omegaT := by simpa using hj
    have e : g⁻¹ * OmegaEightMinus.gen 10 = (OmegaEightMinus.gen 10)⁻¹ *
        (g * (OmegaEightMinus.gen 10)⁻¹)⁻¹ * (OmegaEightMinus.gen 10)⁻¹⁻¹ := by group
    rw [e]
    exact (OmegaEightMinus.conj_mem_omegaT (inv_mem h10)).1 (inv_mem hj')

theorem sig_minus_eq : sig .minus = OmegaEightMinus.gen 10 :=
  (rep_sig (ε := .minus)).1.unique (OmegaEightMinus.rep_gen (by norm_num))

end CFSG.EvenSmallLie.OmegaEight.CPrimeModel
