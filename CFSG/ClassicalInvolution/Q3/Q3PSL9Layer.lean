module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4NS
public import Certificates.Data.ExceptionalSL3

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3PSL9

open CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem zneg_mem_Qns : zneg F ∈ Qns F := by
  have hdet : (-1 : Matrix (Fin 2) (Fin 2) (QE F)).det = 1 := by
    rw [Matrix.det_neg, Matrix.det_one]
    norm_num
  refine ⟨⟨-1, hdet⟩, Subtype.ext ?_⟩
  show Phi (-1 : Matrix (Fin 2) (Fin 2) (QE F)) = -1
  rw [map_neg, map_one]

theorem not_exists_sq_neg_one_of_card_three [Finite F] (hF : Nat.card F = 3) :
    ¬ ∃ i : F, i * i = -1 := by
  have : Fintype F := Fintype.ofFinite F
  rintro ⟨i, hi⟩
  have h := FiniteField.isSquare_neg_one_iff.mp ⟨i, hi.symm⟩
  rw [← Nat.card_eq_fintype_card, hF] at h
  exact h rfl

theorem nonempty_ringEquiv_qe_galoisField_nine [Finite F] (hF : Nat.card F = 3) :
    Nonempty (QE F ≃+* GaloisField 3 2) := by
  have hns := not_exists_sq_neg_one_of_card_three hF
  have : Fact (¬ IsSquare (-1 : F)) := ⟨fun ⟨r, hr⟩ => hns ⟨r, hr.symm⟩⟩
  have : Fintype (QE F) := Fintype.ofFinite _
  have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  refine ⟨FiniteField.ringEquivOfCardEq ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    Nat.card_congr (QuadraticAlgebra.equivProd (-1 : F) 0), Nat.card_prod, hF,
    GaloisField.card 3 2 (by norm_num)]
  norm_num

end CFSG.ClassicalInvolution.Q3.Q3PSL9
