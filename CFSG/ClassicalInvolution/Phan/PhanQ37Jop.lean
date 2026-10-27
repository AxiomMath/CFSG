module

public import CFSG.ClassicalInvolution.Phan.PhanP5Plane
public import CFSG.ClassicalInvolution.Phan.PhanQ9KGeo

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.ModelFacts.MF15

section Defs

@[expose] def jG {R : Type} [CommRing R] (ε : R) (x : V8 R) : V8 R :=
  Sum.elim ![-ε * x (Sum.inl 1), x (Sum.inl 0), -ε * x (Sum.inl 3), x (Sum.inl 2)]
    ![-x (Sum.inr 1), ε * x (Sum.inr 0), -x (Sum.inr 3), ε * x (Sum.inr 2)]

@[expose] def jH {R : Type} [CommRing R] (ε : R) (x : V8 R) : V8 R :=
  Sum.elim ![-ε * x (Sum.inl 1), x (Sum.inl 0), -x (Sum.inr 3), x (Sum.inr 2)]
    ![-x (Sum.inr 1), ε * x (Sum.inr 0), -ε * x (Sum.inl 3), ε * x (Sum.inl 2)]

@[expose] def Pm {R : Type} [CommRing R] (ε : R) : Matrix (Fin 2) (Fin 2) R := !![0, -ε; 1, 0]

end Defs

section Basic

variable {R : Type} [CommRing R] (ε : R)

theorem jG_add (x y : V8 R) : jG ε (x + y) = jG ε x + jG ε y := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [jG] <;> ring

theorem jG_smul (c : R) (x : V8 R) : jG ε (c • x) = c • jG ε x := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [jG] <;> ring

theorem jG_jG (x : V8 R) : jG ε (jG ε x) = (-ε) • x := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [jG]

theorem jH_add (x y : V8 R) : jH ε (x + y) = jH ε x + jH ε y := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [jH] <;> ring

theorem jH_smul (c : R) (x : V8 R) : jH ε (c • x) = c • jH ε x := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [jH] <;> ring

theorem jH_jH (x : V8 R) : jH ε (jH ε x) = (-ε) • x := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [jH]

theorem Pm_mul_Pm : Pm ε * Pm ε = (-ε) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pm, Matrix.mul_apply, Fin.sum_univ_two]

end Basic

section Forms

variable {F : Type} [Field F] (ε : F)

theorem Q8_jG (x : V8 F) : Q8 (jG ε x) = ε * Q8 x := by
  rw [Q8_eq_sum, Q8_eq_sum]
  simp [jG, Fin.sum_univ_four]
  ring

theorem B8_jG (x y : V8 F) : B8 (jG ε x) y = - B8 x (jG ε y) := by
  rw [B8_eq_sum, B8_eq_sum]
  simp [jG, Fin.sum_univ_four]
  ring

theorem Q8_jH (x : V8 F) : Q8 (jH ε x) = ε * Q8 x := by
  rw [Q8_eq_sum, Q8_eq_sum]
  simp [jH, Fin.sum_univ_four]
  ring

theorem B8_jH (x y : V8 F) : B8 (jH ε x) y = - B8 x (jH ε y) := by
  rw [B8_eq_sum, B8_eq_sum]
  simp [jH, Fin.sum_univ_four]
  ring

end Forms

section Frames

variable {F : Type} [Field F]

theorem jG_incl_frame0 (ε : F) (X : Matrix (Fin 2) (Fin 2) F) :
    jG ε ((frame0 (F := F)).incl X) = (frame0 (F := F)).incl (X * Jm ε) := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [jG, Frame.incl_apply, frame0, frameOfVectors, Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂,
      vecXY, Jm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem jG_incl_frame2 (ε : F) (X : Matrix (Fin 2) (Fin 2) F) :
    jG ε ((frame2 (F := F)).incl X) = (frame2 (F := F)).incl (X * Jm ε) := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [jG, Frame.incl_apply, frame2, frameOfVectors, Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂,
      vecXY, Jm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem jG_incl_frame1 (ε : F) (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) (X : Matrix (Fin 2) (Fin 2) F) :
    jG ε ((frame1 ε hε h4).incl X) = (frame1 ε hε h4).incl (X * Jm ε) := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [jG, Frame.incl_apply, frame1, frameOfVectors, Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂,
      vecXY, Jm, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem jG_incl_frame3 (ε : F) (X : Matrix (Fin 2) (Fin 2) F) :
    jG ε ((frame2 (F := F)).swap.incl X) = (frame2 (F := F)).swap.incl (Pm ε * X) := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [jG, Frame.incl_apply, Frame.swap, frame2, frameOfVectors, Frame.e₁, Frame.f₁, Frame.e₂,
      Frame.f₂, vecXY, Pm, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem jH_incl_frame0 (ε : F) (X : Matrix (Fin 2) (Fin 2) F) :
    jH ε ((frame0 (F := F)).incl X) = (frame0 (F := F)).incl (X * Jm ε) := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [jH, Frame.incl_apply, frame0, frameOfVectors, Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂,
      vecXY, Jm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem jH_incl_frame1 (ε : F) (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) (X : Matrix (Fin 2) (Fin 2) F) :
    jH ε ((frame1 ε hε h4).incl X) = (frame1 ε hε h4).incl (X * Jm ε) := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [jH, Frame.incl_apply, frame1, frameOfVectors, Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂,
      vecXY, Jm, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem jH_incl_frame3 (ε : F) (X : Matrix (Fin 2) (Fin 2) F) :
    jH ε ((frame2 (F := F)).swap.incl X) = (frame2 (F := F)).swap.incl (X * Pm ε) := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [jH, Frame.incl_apply, Frame.swap, frame2, frameOfVectors, Frame.e₁, Frame.f₁, Frame.e₂,
      Frame.f₂, vecXY, Pm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem jH_incl_frame2 (ε : F) (X : Matrix (Fin 2) (Fin 2) F) :
    jH ε ((frame2 (F := F)).incl X) = (frame2 (F := F)).incl (Jm ε * X) := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [jH, Frame.incl_apply, frame2, frameOfVectors, Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂,
      vecXY, Jm, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

end Frames

section Sim

open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def jSim (ε : F) (hε : ε ≠ 0) : SemiSim (quadPlus 4 F) where
  toFun := jG ε
  φ := RingEquiv.refl F
  μ := ε
  μ_ne := hε
  map_add' := jG_add ε
  map_smul' c v := jG_smul ε c v
  bijective := by
    constructor
    · intro x y h
      have h2 := congrArg (jG ε) h
      rw [jG_jG, jG_jG] at h2
      exact smul_right_injective _ (neg_ne_zero.2 hε) h2
    · intro y
      refine ⟨(-ε)⁻¹ • jG ε y, ?_⟩
      show jG ε ((-ε)⁻¹ • jG ε y) = y
      rw [jG_smul, jG_jG, smul_smul, inv_mul_cancel₀ (neg_ne_zero.2 hε), one_smul]
  map_Q' v := Q8_jG ε v

@[expose] def hSim (ε : F) (hε : ε ≠ 0) : SemiSim (quadPlus 4 F) where
  toFun := jH ε
  φ := RingEquiv.refl F
  μ := ε
  μ_ne := hε
  map_add' := jH_add ε
  map_smul' c v := jH_smul ε c v
  bijective := by
    constructor
    · intro x y h
      have h2 := congrArg (jH ε) h
      rw [jH_jH, jH_jH] at h2
      exact smul_right_injective _ (neg_ne_zero.2 hε) h2
    · intro y
      refine ⟨(-ε)⁻¹ • jH ε y, ?_⟩
      show jH ε ((-ε)⁻¹ • jH ε y) = y
      rw [jH_smul, jH_jH, smul_smul, inv_mul_cancel₀ (neg_ne_zero.2 hε), one_smul]
  map_Q' v := Q8_jH ε v

theorem surj_mulRight_Jm {ε : F} (hε : ε ≠ 0) :
    Function.Surjective (fun X : Matrix (Fin 2) (Fin 2) F => X * Jm ε) := by
  intro Y
  refine ⟨(-ε)⁻¹ • (Y * Jm ε), ?_⟩
  simp only [Matrix.smul_mul, Matrix.mul_assoc, Jm_mul_Jm, Matrix.mul_smul, Matrix.mul_one,
    smul_smul]
  rw [inv_mul_cancel₀ (neg_ne_zero.2 hε), one_smul]

theorem surj_mulLeft_Jm {ε : F} (hε : ε ≠ 0) :
    Function.Surjective (fun X : Matrix (Fin 2) (Fin 2) F => Jm ε * X) := by
  intro Y
  refine ⟨(-ε)⁻¹ • (Jm ε * Y), ?_⟩
  simp only [Matrix.mul_smul, ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.smul_mul, Matrix.one_mul,
    smul_smul]
  rw [inv_mul_cancel₀ (neg_ne_zero.2 hε), one_smul]

theorem surj_mulRight_Pm {ε : F} (hε : ε ≠ 0) :
    Function.Surjective (fun X : Matrix (Fin 2) (Fin 2) F => X * Pm ε) := by
  intro Y
  refine ⟨(-ε)⁻¹ • (Y * Pm ε), ?_⟩
  simp only [Matrix.smul_mul, Matrix.mul_assoc, Pm_mul_Pm, Matrix.mul_smul, Matrix.mul_one,
    smul_smul]
  rw [inv_mul_cancel₀ (neg_ne_zero.2 hε), one_smul]

theorem surj_mulLeft_Pm {ε : F} (hε : ε ≠ 0) :
    Function.Surjective (fun X : Matrix (Fin 2) (Fin 2) F => Pm ε * X) := by
  intro Y
  refine ⟨(-ε)⁻¹ • (Pm ε * Y), ?_⟩
  simp only [Matrix.mul_smul, ← Matrix.mul_assoc, Pm_mul_Pm, Matrix.smul_mul, Matrix.one_mul,
    smul_smul]
  rw [inv_mul_cancel₀ (neg_ne_zero.2 hε), one_smul]

theorem La_eq_embLin (fr : Frame (quadPlus 4 F)) (M : SL(2, F)) (v : V8 F) :
    fr.La M v = fr.embLin (LinearMap.mulLeft F (M : Matrix (Fin 2) (Fin 2) F)) v := by
  rw [Frame.La_apply, Frame.embLin_apply]
  rfl

theorem jG_La_comm_of_incl {ε : F} (hε : ε ≠ 0) (fr : Frame (quadPlus 4 F))
    (h : ∀ X, jG ε (fr.incl X) = fr.incl (X * Jm ε)) (M : SL(2, F)) (v : V8 F) :
    jG ε (fr.La M v) = fr.La M (jG ε v) := by
  rw [La_eq_embLin, La_eq_embLin]
  exact comm_embLin fr (jSim ε hε) (fun X => X * Jm ε) h (surj_mulRight_Jm hε)
    (LinearMap.mulLeft F (M : Matrix (Fin 2) (Fin 2) F))
    (fun X => by simp [Matrix.mul_assoc]) v

theorem jH_La_comm_of_incl {ε : F} (hε : ε ≠ 0) (fr : Frame (quadPlus 4 F))
    (h : ∀ X, jH ε (fr.incl X) = fr.incl (X * Jm ε)) (M : SL(2, F)) (v : V8 F) :
    jH ε (fr.La M v) = fr.La M (jH ε v) := by
  rw [La_eq_embLin, La_eq_embLin]
  exact comm_embLin fr (hSim ε hε) (fun X => X * Jm ε) h (surj_mulRight_Jm hε)
    (LinearMap.mulLeft F (M : Matrix (Fin 2) (Fin 2) F))
    (fun X => by simp [Matrix.mul_assoc]) v

theorem jH_La_comm_of_incl_Pm {ε : F} (hε : ε ≠ 0) (fr : Frame (quadPlus 4 F))
    (h : ∀ X, jH ε (fr.incl X) = fr.incl (X * Pm ε)) (M : SL(2, F)) (v : V8 F) :
    jH ε (fr.La M v) = fr.La M (jH ε v) := by
  rw [La_eq_embLin, La_eq_embLin]
  exact comm_embLin fr (hSim ε hε) (fun X => X * Pm ε) h (surj_mulRight_Pm hε)
    (LinearMap.mulLeft F (M : Matrix (Fin 2) (Fin 2) F))
    (fun X => by simp [Matrix.mul_assoc]) v

theorem jG_La3_comm_iff {ε : F} (hε : ε ≠ 0) (M : SL(2, F)) :
    (∀ v : V8 F, jG ε ((frame2 (F := F)).swap.La M v) = (frame2 (F := F)).swap.La M (jG ε v)) ↔
      (M : Matrix (Fin 2) (Fin 2) F) * Pm ε = Pm ε * (M : Matrix (Fin 2) (Fin 2) F) := by
  constructor
  · intro h
    have h1 := h ((frame2 (F := F)).swap.incl 1)
    rw [Frame.La_apply_incl, jG_incl_frame3, jG_incl_frame3, Frame.La_apply_incl] at h1
    have h2 := congrArg (frame2 (F := F)).swap.coords h1
    rw [Frame.coords_incl, Frame.coords_incl] at h2
    simpa using h2.symm
  · intro hMP v
    rw [La_eq_embLin, La_eq_embLin]
    exact comm_embLin (frame2 (F := F)).swap (jSim ε hε) (fun X => Pm ε * X)
      (jG_incl_frame3 ε) (surj_mulLeft_Pm hε) (LinearMap.mulLeft F (M : Matrix (Fin 2) (Fin 2) F))
      (fun X => by
        simp only [LinearMap.mulLeft_apply]
        rw [← Matrix.mul_assoc, ← hMP, Matrix.mul_assoc]) v

theorem jH_La2_comm_iff {ε : F} (hε : ε ≠ 0) (M : SL(2, F)) :
    (∀ v : V8 F, jH ε ((frame2 (F := F)).La M v) = (frame2 (F := F)).La M (jH ε v)) ↔
      (M : Matrix (Fin 2) (Fin 2) F) * Jm ε = Jm ε * (M : Matrix (Fin 2) (Fin 2) F) := by
  constructor
  · intro h
    have h1 := h ((frame2 (F := F)).incl 1)
    rw [Frame.La_apply_incl, jH_incl_frame2, jH_incl_frame2, Frame.La_apply_incl] at h1
    have h2 := congrArg (frame2 (F := F)).coords h1
    rw [Frame.coords_incl, Frame.coords_incl] at h2
    simpa using h2.symm
  · intro hMP v
    rw [La_eq_embLin, La_eq_embLin]
    exact comm_embLin (frame2 (F := F)) (hSim ε hε) (fun X => Jm ε * X)
      (jH_incl_frame2 ε) (surj_mulLeft_Jm hε) (LinearMap.mulLeft F (M : Matrix (Fin 2) (Fin 2) F))
      (fun X => by
        simp only [LinearMap.mulLeft_apply]
        rw [← Matrix.mul_assoc, ← hMP, Matrix.mul_assoc]) v

end Sim

end CFSG.ClassicalInvolution.PhanQ
