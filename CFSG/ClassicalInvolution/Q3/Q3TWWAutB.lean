module

public import CFSG.ClassicalInvolution.Q3.Q3ZAutAbs
public import CFSG.ClassicalInvolution.WeakCT.Blocks
public import CFSG.LieType.CurtisTits.SpecialLinear

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.Q3.Q3Z
open CFSG.ClassicalInvolution.WeakCT (blockSL coe_blockSL_three_zero coe_blockSL_three_one)
open scoped MatrixGroups

local notation "bA0" => (blockSL (ZMod 3) 3 2 0 (by omega) : SL(2, ZMod 3) →* SL(3, ZMod 3))
local notation "bA1" => (blockSL (ZMod 3) 3 2 1 (by omega) : SL(2, ZMod 3) →* SL(3, ZMod 3))
local notation "sB" =>
  (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1) : SL(2, ZMod 3) →* StatedSp 2 (ZMod 3))
local notation "lB2" => (longBlock (ZMod 3) 2 1 : SL(2, ZMod 3) →* StatedSp 2 (ZMod 3))

section Generic

variable {K : Type} [Field K]

@[expose] def twAg (K : Type) [Field K] : SL(3, K) := ⟨!![-1, 0, 0; 0, -1, 0; 0, 0, 1], by
  rw [Matrix.det_fin_three]; simp⟩

theorem twAg_mul_self : twAg K * twAg K = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twAg, Matrix.mul_apply, Fin.sum_univ_three]

theorem twAg_inv : (twAg K)⁻¹ = twAg K := inv_eq_of_mul_eq_one_right twAg_mul_self

@[expose] def flipSLg (A : SL(2, K)) : SL(2, K) :=
  ⟨!![(A : Matrix (Fin 2) (Fin 2) K) 0 0, -(A : Matrix (Fin 2) (Fin 2) K) 0 1;
    -(A : Matrix (Fin 2) (Fin 2) K) 1 0, (A : Matrix (Fin 2) (Fin 2) K) 1 1], by
    have h := A.2
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    linear_combination h⟩

theorem flipSLg_mul (A B : SL(2, K)) : flipSLg (A * B) = flipSLg A * flipSLg B := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul (flipSLg A) (flipSLg B)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flipSLg, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem flipSLg_one : flipSLg (1 : SL(2, K)) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flipSLg]

theorem twAg_conj_bA0 (A : SL(2, K)) :
    twAg K * blockSL K 3 2 0 (by omega) A * (twAg K)⁻¹ = blockSL K 3 2 0 (by omega) A := by
  rw [twAg_inv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twAg, Matrix.mul_apply, Fin.sum_univ_three, coe_blockSL_three_zero]

theorem twAg_conj_bA1 (A : SL(2, K)) :
    twAg K * blockSL K 3 2 1 (by omega) A * (twAg K)⁻¹ =
      blockSL K 3 2 1 (by omega) (flipSLg A) := by
  rw [twAg_inv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_blockSL_three_one A, coe_blockSL_three_one (flipSLg A)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twAg, flipSLg, Matrix.mul_apply, Fin.sum_univ_three]

theorem flipSLg_flipSLg (A : SL(2, K)) : flipSLg (flipSLg A) = A := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flipSLg]

end Generic

@[expose] def flipHom : SL(2, ZMod 3) →* SL(2, ZMod 3) where
  toFun := flipSLg
  map_one' := flipSLg_one
  map_mul' := flipSLg_mul

theorem absD0_inv_conj_xp : (absD 0)⁻¹ * autXp * absD 0 = autXm⁻¹ := by decide +kernel

theorem absD0_inv_conj_xm : (absD 0)⁻¹ * autXm * absD 0 = autXp⁻¹ := by decide +kernel

theorem absD0_conj_xp : absD 0 * autXp * (absD 0)⁻¹ = autXm⁻¹ := by decide +kernel

theorem absD0_conj_xm : absD 0 * autXm * (absD 0)⁻¹ = autXp⁻¹ := by decide +kernel

theorem flip_autXp : flipSLg autXp = autXp⁻¹ := by decide +kernel

theorem flip_autXm : flipSLg autXm = autXm⁻¹ := by decide +kernel

@[expose] def Absorbs (α : SL(2, ZMod 3) ≃* SL(2, ZMod 3)) : Prop :=
  ∃ (t : SL(3, ZMod 3)) (B : StatedSp 2 (ZMod 3)),
    (∀ A, t * bA0 A * t⁻¹ = bA0 A) ∧
    (∀ A, ∃ A', t * bA1 A * t⁻¹ = bA1 A') ∧
    (∀ A', ∃ A, t * bA1 A * t⁻¹ = bA1 A') ∧
    (∀ A A', t * bA1 A * t⁻¹ = bA1 A' → B⁻¹ * lB2 A * B = lB2 (α.symm A')) ∧
    (∀ A, ∃ A', B * sB A * B⁻¹ = sB A') ∧ (∀ A, ∃ A', B⁻¹ * sB A * B = sB A')

theorem blockSL_one_injective : Function.Injective (bA1) :=
  CFSG.ClassicalInvolution.WeakCT.blockSL_injective (K := ZMod 3) (m := 3) (k := 2) (i := 1)
    (by omega)

theorem absorbs_id (α : SL(2, ZMod 3) ≃* SL(2, ZMod 3)) (hp : α autXp = autXp)
    (hm : α autXm = autXm) : Absorbs α := by
  have hα : α = MulEquiv.refl _ := alpha_eq_of_gens hp hm
  refine ⟨1, 1, fun A => by simp, fun A => ⟨A, by simp⟩, fun A' => ⟨A', by simp⟩, ?_,
    fun A => ⟨A, by simp⟩, fun A => ⟨A, by simp⟩⟩
  intro A A' h
  have h1 : A' = A := blockSL_one_injective (by simpa using h.symm)
  subst h1
  subst hα
  simp

theorem absorbs_flip (α : SL(2, ZMod 3) ≃* SL(2, ZMod 3)) (hp : α autXp = autXp⁻¹)
    (hm : α autXm = autXm⁻¹) : Absorbs α := by
  have hα : ∀ A, α A = flipSLg A := fun A => DFunLike.congr_fun
    (hom_ext_of_gens (f := α.toMonoidHom) (g := flipHom) (by simpa [flipHom, flip_autXp] using hp)
      (by simpa [flipHom, flip_autXm] using hm)) A
  refine ⟨twAg (ZMod 3), 1, twAg_conj_bA0, fun A => ⟨flipSLg A, twAg_conj_bA1 A⟩,
    fun A' => ⟨flipSLg A', by rw [twAg_conj_bA1, flipSLg_flipSLg]⟩, ?_,
    fun A => ⟨A, by simp⟩, fun A => ⟨A, by simp⟩⟩
  intro A A' h
  rw [twAg_conj_bA1] at h
  have h1 : A' = flipSLg A := (blockSL_one_injective h).symm
  subst h1
  have h2 : α.symm (flipSLg A) = A := by
    rw [MulEquiv.symm_apply_eq, hα]
  rw [h2]
  simp

theorem absElt0_short (A : SL(2, ZMod 3)) :
    (∃ A', absElt 0 * sB A * (absElt 0)⁻¹ = sB A') ∧
      ∃ A', (absElt 0)⁻¹ * sB A * absElt 0 = sB A' := by
  let α₀ : SL(2, ZMod 3) ≃* SL(2, ZMod 3) := MulAut.conj (absD 0)
  have hp : α₀ autXp = absImgP 0 := by
    show absD 0 * autXp * (absD 0)⁻¹ = absImgP 0
    rw [absD0_conj_xp]
    rfl
  have hm : α₀ autXm = absImgM 0 := by
    show absD 0 * autXm * (absD 0)⁻¹ = absImgM 0
    rw [absD0_conj_xm]
    rfl
  refine ⟨⟨_, absElt_short 0 α₀ hp hm A⟩, α₀.symm A, ?_⟩
  have h := absElt_short 0 α₀ hp hm (α₀.symm A)
  rw [α₀.apply_symm_apply] at h
  rw [← h]
  group

theorem absorbs_swapInv (α : SL(2, ZMod 3) ≃* SL(2, ZMod 3)) (hp : α autXp = autXm⁻¹)
    (hm : α autXm = autXp⁻¹) : Absorbs α := by
  have hα : ∀ A, α ((absD 0)⁻¹ * A * absD 0) = A := fun A => by
    have := DFunLike.congr_fun
      (hom_ext_of_gens
        (f := α.toMonoidHom.comp (MulAut.conj (absD 0)⁻¹).toMonoidHom) (g := MonoidHom.id _)
        (by simp [absD0_inv_conj_xp, hm]) (by simp [absD0_inv_conj_xm, hp])) A
    simpa using this
  refine ⟨1, absElt 0, fun A => by simp, fun A => ⟨A, by simp⟩, fun A' => ⟨A', by simp⟩, ?_,
    fun A => (absElt0_short A).1, fun A => (absElt0_short A).2⟩
  intro A A' h
  have h1 : A' = A := blockSL_one_injective (by simpa using h.symm)
  rw [h1, absElt_long_inv, (MulEquiv.symm_apply_eq α).2 (hα A).symm]

theorem absorbs_swap (α : SL(2, ZMod 3) ≃* SL(2, ZMod 3)) (hp : α autXp = autXm)
    (hm : α autXm = autXp) : Absorbs α := by
  have hα : ∀ A, α ((absD 0)⁻¹ * A * absD 0) = flipSLg A := fun A => by
    have := DFunLike.congr_fun
      (hom_ext_of_gens
        (f := α.toMonoidHom.comp (MulAut.conj (absD 0)⁻¹).toMonoidHom) (g := flipHom)
        (by simp [absD0_inv_conj_xp, hm, flipHom, flip_autXp])
        (by simp [absD0_inv_conj_xm, hp, flipHom, flip_autXm])) A
    simpa [show flipHom A = flipSLg A from rfl] using this
  refine ⟨twAg (ZMod 3), absElt 0, twAg_conj_bA0, fun A => ⟨flipSLg A, twAg_conj_bA1 A⟩,
    fun A' => ⟨flipSLg A', by rw [twAg_conj_bA1, flipSLg_flipSLg]⟩, ?_,
    fun A => (absElt0_short A).1, fun A => (absElt0_short A).2⟩
  intro A A' h
  rw [twAg_conj_bA1] at h
  have h1 : A' = flipSLg A := (blockSL_one_injective h).symm
  rw [h1, absElt_long_inv, (MulEquiv.symm_apply_eq α).2 (hα A).symm]

theorem absorb_b (k : Fin 4) (α : SL(2, ZMod 3) ≃* SL(2, ZMod 3)) (hp : α autXp = absImgP k)
    (hm : α autXm = absImgM k) : Absorbs α := by
  fin_cases k
  · exact absorbs_swapInv α (by simpa [absImgP] using hp) (by simpa [absImgM] using hm)
  · exact absorbs_flip α (by simpa [absImgP] using hp) (by simpa [absImgM] using hm)
  · exact absorbs_id α (by simpa [absImgP] using hp) (by simpa [absImgM] using hm)
  · exact absorbs_swap α (by simpa [absImgP] using hp) (by simpa [absImgM] using hm)

end CFSG.ClassicalInvolution.Q3.Q3TW
