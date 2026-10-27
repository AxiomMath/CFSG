module

public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LSU02
public import CFSG.ClassicalInvolution.ModelFacts.TG3SmallSUGen

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.Q3.Q3PP (F9 card_F9)

section Gen

variable {i : F9}

@[expose] noncomputable def aElt (hi : i * i = -1) (hσi : unitaryInvolution F9 3 1 i = -i) :
    Su F9 3 1 2 :=
  have hσi' : (frobenius F9 3) i = -i := by simpa using hσi
  Models.mkSU F9 3 1 !![-i, 0; 0, i] (by
    rw [Matrix.det_fin_two_of]
    linear_combination -hi) (by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two, hσi'] <;> linear_combination -hi)

theorem suMat_aElt (hi : i * i = -1) (hσi : unitaryInvolution F9 3 1 i = -i) :
    suMat (aElt hi hσi) = !![-i, 0; 0, i] := rfl

theorem aElt_mul_self (hi : i * i = -1) (hσi : unitaryInvolution F9 3 1 i = -i) :
    aElt hi hσi * aElt hi hσi = negOneSU F9 3 1 := by
  apply suMat_injective
  rw [suMat_mul, suMat_aElt, suMat_negOneSU]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination hi

theorem suMat_blockEmb_two_four (A : Su F9 3 1 2) :
    suMat (blockEmb F9 3 1 4 2 2 (by norm_num) A) =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, suMat A 0 0, suMat A 0 1;
        0, 0, suMat A 1 0, suMat A 1 1] := by
  rw [suMat_blockEmb]
  ext a b
  rw [Phan.blockMat_apply]
  fin_cases a <;> fin_cases b <;> simp

theorem suMat_aElt_pair (hi : i * i = -1) (hσi : unitaryInvolution F9 3 1 i = -i) :
    suMat (blockEmb F9 3 1 4 2 0 (by norm_num) (aElt hi hσi) *
        blockEmb F9 3 1 4 2 2 (by norm_num) (aElt hi hσi)) =
      i • zMat F9 4 pair02.1 := by
  rw [suMat_mul, suMat_blockEmb_zero_four, suMat_blockEmb_two_four, zMat_pair02]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, suMat_aElt]

theorem centralizer_le_of_suMat_smul {J w : Su F9 3 1 4} {c : F9} (hc : c ≠ 0)
    (hJ : suMat J = c • suMat w) :
    Subgroup.centralizer ({J} : Set (Su F9 3 1 4)) ≤
      Subgroup.centralizer ({w} : Set (Su F9 3 1 4)) :=
  fun g hg => by
  rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
  apply suMat_injective
  have h1 := congrArg suMat hg
  rw [suMat_mul, suMat_mul, hJ, Matrix.mul_smul, Matrix.smul_mul] at h1
  rw [suMat_mul, suMat_mul]
  exact smul_right_injective _ hc h1

theorem centralizer_pair01_sup_pair02 :
    Subgroup.centralizer ({zEltU F9 3 1 pair01} : Set (Su F9 3 1 4)) ⊔
      Subgroup.centralizer ({zEltU F9 3 1 pair02} : Set (Su F9 3 1 4)) = ⊤ := by
  obtain ⟨i, hi, hσi⟩ := Q3MFOU4.exists_iota
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  have hgen := ModelFacts.TG3.su4_std_gen card_F9 (by norm_num) hi hσi (aElt hi hσi)
    (aElt hi hσi) (aElt_mul_self hi hσi) (aElt_mul_self hi hσi)
  rw [← zEltU_pair01_eq] at hgen
  rw [eq_top_iff, ← hgen]
  exact sup_le_sup le_rfl (centralizer_le_of_suMat_smul hi0
    (by rw [suMat_zEltU]; exact suMat_aElt_pair hi hσi))

end Gen

end CFSG.ClassicalInvolution.Q3.Q3AM
