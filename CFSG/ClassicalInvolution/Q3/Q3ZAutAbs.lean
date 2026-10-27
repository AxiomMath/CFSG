module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.ClassicalInvolution.Q3.Q3ZAutFin

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Steinberg.Sp (blockMat)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

@[expose] def absMat : Fin 4 → Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  ![fromBlocks 0 1 (-1) 0, fromBlocks (diagonal ![1, -1]) 0 0 (diagonal ![1, -1]), 1,
    fromBlocks 0 (diagonal ![1, -1]) (diagonal ![-1, 1]) 0]

@[expose] def absImgP : Fin 4 → SL(2, ZMod 3) := ![autXm⁻¹, autXp⁻¹, autXp, autXm]

@[expose] def absImgM : Fin 4 → SL(2, ZMod 3) := ![autXp⁻¹, autXm⁻¹, autXm, autXp]

theorem evalW_gluingA_castLE (k : Fin 4) :
    evalW gluingAssign (gluingA (Fin.castLE (by norm_num) k)) = absImgP k := by
  revert k
  decide +kernel

theorem evalW_gluingB_castLE (k : Fin 4) :
    evalW gluingAssign (gluingB (Fin.castLE (by norm_num) k)) = absImgM k := by
  revert k
  decide +kernel

@[expose] def absD : Fin 4 → SL(2, ZMod 3) :=
  ![⟨!![0, 1; 2, 0], by decide⟩, ⟨!![2, 0; 0, 2], by decide⟩, 1, ⟨!![0, 2; 1, 0], by decide⟩]

@[expose] def shortMat (A : SL(2, ZMod 3)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  fromBlocks (blockMat (0 : Fin 2) 1 (A : Matrix (Fin 2) (Fin 2) (ZMod 3))) 0 0
    (blockMat (0 : Fin 2) 1 ((A⁻¹ : SL(2, ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)))ᵀ

@[expose] def longMat (A : SL(2, ZMod 3)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  blockMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2)) (A : Matrix (Fin 2) (Fin 2) (ZMod 3))

theorem mat_short (A : SL(2, ZMod 3)) :
    mat 2 (ZMod 3) (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1) A) = shortMat A :=
  mat_shortBlock _ A

theorem mat_long (A : SL(2, ZMod 3)) :
    mat 2 (ZMod 3) (longBlock (ZMod 3) 2 1 A) = longMat A :=
  mat_longBlock 1 A

theorem absMat_symp (k : Fin 4) : (absMat k)ᵀ * gram (ZMod 3) 2 * absMat k = gram (ZMod 3) 2 := by
  revert k
  decide +kernel

@[expose] noncomputable def absElt (k : Fin 4) : StatedSp 2 (ZMod 3) :=
  ofSymplecticMat (absMat k) (absMat_symp k)

theorem mat_absElt (k : Fin 4) : mat 2 (ZMod 3) (absElt k) = absMat k := rfl

theorem conj_eq_of_mat {B X Y : StatedSp 2 (ZMod 3)}
    (h : mat 2 (ZMod 3) B * mat 2 (ZMod 3) X = mat 2 (ZMod 3) Y * mat 2 (ZMod 3) B) :
    B * X * B⁻¹ = Y := by
  rw [mul_inv_eq_iff_eq_mul]
  exact mat_injective (by rw [map_mul, map_mul]; exact h)

theorem absMat_shortMat_p (k : Fin 4) :
    absMat k * shortMat autXp = shortMat (absImgP k) * absMat k := by
  revert k
  decide +kernel

theorem absMat_shortMat_m (k : Fin 4) :
    absMat k * shortMat autXm = shortMat (absImgM k) * absMat k := by
  revert k
  decide +kernel

theorem absElt_short (k : Fin 4) (α : SL(2, ZMod 3) ≃* SL(2, ZMod 3))
    (hp : α autXp = absImgP k) (hm : α autXm = absImgM k) (A : SL(2, ZMod 3)) :
    absElt k * shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1) A * (absElt k)⁻¹ =
      shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1) (α A) := by
  have key : (MulAut.conj (absElt k)).toMonoidHom.comp
        (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1)) =
      (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1)).comp α.toMonoidHom := by
    refine hom_ext_of_gens ?_ ?_
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hp]
      exact conj_eq_of_mat (by rw [mat_absElt, mat_short, mat_short]; exact absMat_shortMat_p k)
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hm]
      exact conj_eq_of_mat (by rw [mat_absElt, mat_short, mat_short]; exact absMat_shortMat_m k)
  simpa using DFunLike.congr_fun key A

theorem absMat_longMat_p (k : Fin 4) :
    absMat k * longMat autXp = longMat (absD k * autXp * (absD k)⁻¹) * absMat k := by
  revert k
  decide +kernel

theorem absMat_longMat_m (k : Fin 4) :
    absMat k * longMat autXm = longMat (absD k * autXm * (absD k)⁻¹) * absMat k := by
  revert k
  decide +kernel

theorem absElt_long (k : Fin 4) (A : SL(2, ZMod 3)) :
    absElt k * longBlock (ZMod 3) 2 1 A * (absElt k)⁻¹ =
      longBlock (ZMod 3) 2 1 (absD k * A * (absD k)⁻¹) := by
  have key : (MulAut.conj (absElt k)).toMonoidHom.comp (longBlock (ZMod 3) 2 1) =
      (longBlock (ZMod 3) 2 1).comp (MulAut.conj (absD k)).toMonoidHom := by
    refine hom_ext_of_gens ?_ ?_
    · simp only [MonoidHom.comp_apply]
      exact conj_eq_of_mat (by rw [mat_absElt, mat_long, mat_long]; exact absMat_longMat_p k)
    · simp only [MonoidHom.comp_apply]
      exact conj_eq_of_mat (by rw [mat_absElt, mat_long, mat_long]; exact absMat_longMat_m k)
  simpa using DFunLike.congr_fun key A

theorem absElt_long_inv (k : Fin 4) (A : SL(2, ZMod 3)) :
    (absElt k)⁻¹ * longBlock (ZMod 3) 2 1 A * absElt k =
      longBlock (ZMod 3) 2 1 ((absD k)⁻¹ * A * absD k) := by
  have h := absElt_long k ((absD k)⁻¹ * A * absD k)
  have e : absD k * ((absD k)⁻¹ * A * absD k) * (absD k)⁻¹ = A := by group
  rw [e] at h
  rw [← h]
  group

theorem absorbed_of_pair (k : Fin 4) (α : SL(2, ZMod 3) ≃* SL(2, ZMod 3))
    (hp : α autXp = absImgP k) (hm : α autXm = absImgM k) :
    ∃ B : StatedSp 2 (ZMod 3),
      (∀ A : SL(2, ZMod 3),
        B * shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1) A * B⁻¹ =
          shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1) (α A)) ∧
      ∀ A : SL(2, ZMod 3),
        (∃ A' : SL(2, ZMod 3), B * longBlock (ZMod 3) 2 1 A * B⁻¹ = longBlock (ZMod 3) 2 1 A') ∧
          ∃ A'' : SL(2, ZMod 3), B⁻¹ * longBlock (ZMod 3) 2 1 A * B = longBlock (ZMod 3) 2 1 A'' :=
  ⟨absElt k, absElt_short k α hp hm, fun A => ⟨⟨_, absElt_long k A⟩, ⟨_, absElt_long_inv k A⟩⟩⟩

end CFSG.ClassicalInvolution.Q3.Q3Z
