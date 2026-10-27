module

public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardRowCoordinates

public section

open Matrix Subgroup
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open CFSG.LocalAnalysis.EvenBN.LinearThree

namespace CFSG.ComponentClassification.GS79bSec5

@[expose] noncomputable def colSLHom (F : Type) [Field F] :
    Multiplicative (Fin 2 → F) →* Matrix.SpecialLinearGroup (Fin 3) F where
  toFun v := unipU F 0 (Multiplicative.toAdd v 1) (Multiplicative.toAdd v 0)
  map_one' := by simp [unipU_zero]
  map_mul' v w := by
    simp only [toAdd_mul, Pi.add_apply]
    rw [unipU_mul]
    simp

theorem colSLHom_range (F : Type) [Field F] : (colSLHom F).range = unipTwo F := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨Multiplicative.toAdd v 1, Multiplicative.toAdd v 0, rfl⟩
  · rintro ⟨b, c, rfl⟩
    refine ⟨Multiplicative.ofAdd ![c, b], ?_⟩
    simp [colSLHom]

theorem proj_comp_colSLHom (F : Type) [Field F] :
    (proj 3 F).comp (colSLHom F) = radCoord F 1 := by
  ext v
  exact radCoord_one_apply v

theorem leviTwo_conj_colSLHom {F : Type} [Field F] (B : Matrix.SpecialLinearGroup (Fin 2) F)
    (v : Multiplicative (Fin 2 → F)) :
    leviTwo F B * colSLHom F v * (leviTwo F B)⁻¹ =
      colSLHom F (Multiplicative.ofAdd
        ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd v)) := by
  let b : F := Multiplicative.toAdd v 1
  let c : F := Multiplicative.toAdd v 0
  have h := leviTwo_mul_unipU B b c
  change leviTwo F B * unipU F 0 b c * (leviTwo F B)⁻¹ =
    unipU F 0 (Multiplicative.toAdd (Multiplicative.ofAdd
      ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd v)) 1)
      (Multiplicative.toAdd (Multiplicative.ofAdd
        ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd v)) 0)
  rw [toAdd_ofAdd]
  rw [mul_inv_eq_iff_eq_mul.2 h]
  congr 1 <;> simp [b, c, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem torSLOne_conj_colSLHom {F : Type} [Field F] (l : Fˣ)
    (v : Multiplicative (Fin 2 → F)) :
    torSLOne F l * colSLHom F v * (torSLOne F l)⁻¹ =
      colSLHom F (Multiplicative.ofAdd (((l : F) ^ 3) • Multiplicative.toAdd v)) := by
  let b : F := Multiplicative.toAdd v 1
  let c : F := Multiplicative.toAdd v 0
  have h := torSL_one_mul_unipU l b c
  change torSLOne F l * unipU F 0 b c =
    unipU F 0 ((l : F) ^ 3 * b) ((l : F) ^ 3 * c) * torSLOne F l at h
  change torSLOne F l * unipU F 0 b c * (torSLOne F l)⁻¹ =
    unipU F 0 (Multiplicative.toAdd (Multiplicative.ofAdd
      (((l : F) ^ 3) • Multiplicative.toAdd v)) 1)
      (Multiplicative.toAdd (Multiplicative.ofAdd
        (((l : F) ^ 3) • Multiplicative.toAdd v)) 0)
  rw [toAdd_ofAdd]
  rw [mul_inv_eq_iff_eq_mul.2 h]
  rfl

@[expose] noncomputable def radSLHom (F : Type) [Field F] (i : Fin 2) :
    Multiplicative (Fin 2 → F) →* Matrix.SpecialLinearGroup (Fin 3) F :=
  ![rowSLHom F, colSLHom F] i

theorem proj_comp_radSLHom (F : Type) [Field F] (i : Fin 2) :
    (proj 3 F).comp (radSLHom F i) = radCoord F i := by
  revert i
  rw [Fin.forall_fin_two]
  exact ⟨proj_comp_rowSLHom F, proj_comp_colSLHom F⟩

theorem range_radSLHom (F : Type) [Field F] (i : Fin 2) :
    (radSLHom F i).range = ![unipOne F, unipTwo F] i := by
  revert i
  rw [Fin.forall_fin_two]
  exact ⟨rowSLHom_range F, colSLHom_range F⟩

theorem levi_conj_radSLHom {F : Type} [Field F] (i : Fin 2)
    (B : Matrix.SpecialLinearGroup (Fin 2) F) (v : Multiplicative (Fin 2 → F)) :
    levi F i B * radSLHom F i v * (levi F i B)⁻¹ =
      radSLHom F i (Multiplicative.ofAdd
        ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd v)) := by
  revert i
  rw [Fin.forall_fin_two]
  exact ⟨leviOne_conj_rowSLHom B v, leviTwo_conj_colSLHom B v⟩

theorem torSL_conj_radSLHom {F : Type} [Field F] (i : Fin 2) (l : Fˣ)
    (v : Multiplicative (Fin 2 → F)) :
    torSL F i l * radSLHom F i v * (torSL F i l)⁻¹ =
      radSLHom F i (Multiplicative.ofAdd (((l : F) ^ 3) • Multiplicative.toAdd v)) := by
  revert i
  rw [Fin.forall_fin_two]
  exact ⟨torSLZero_conj_rowSLHom l v, torSLOne_conj_colSLHom l v⟩

end CFSG.ComponentClassification.GS79bSec5

end
