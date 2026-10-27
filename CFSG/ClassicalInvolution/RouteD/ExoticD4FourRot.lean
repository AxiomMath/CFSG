module

public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourMat
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Fundamental
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Pairs
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalGroups.Orthogonal.Derived
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.Open.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open QuadraticMap Matrix CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Basis

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem polar_incl_incl (F₀ : OFrame Q) (X Y : Matrix (Fin 2) (Fin 2) F) :
    polar Q (F₀.incl X) (F₀.incl Y) = polarDet X Y := by
  rw [Frame.polar_incl_right, Frame.coords_incl]
  simp only [polarDet]
  ring

@[expose] def bV (F₁ F₃ : OFrame Q) (a b : F) : Fin 4 ⊕ Fin 4 → V :=
  Sum.elim (fun j => F₁.incl (mVec a b j)) (fun j => F₃.incl (mVec a b j))

variable {F₁ F₃ : OFrame Q} {a b : F}

theorem Q_bV (hab : a ^ 2 + b ^ 2 = -1) (i : Fin 4 ⊕ Fin 4) : Q (bV F₁ F₃ a b i) = 1 := by
  rcases i with j | j
  · simp only [bV, Sum.elim_inl]
    rw [Frame.Q_incl, det_mVec hab]
  · simp only [bV, Sum.elim_inr]
    rw [Frame.Q_incl, det_mVec hab]

theorem polar_bV (hab : a ^ 2 + b ^ 2 = -1) (horth : ∀ X Y, polar Q (F₁.incl X) (F₃.incl Y) = 0)
    (i k : Fin 4 ⊕ Fin 4) :
    polar Q (bV F₁ F₃ a b i) (bV F₁ F₃ a b k) = if i = k then 2 else 0 := by
  rcases i with j | j <;> rcases k with k | k
  · simp only [bV, Sum.elim_inl, polar_incl_incl, polarDet_mVec hab, Sum.inl.injEq]
  · simp only [bV, Sum.elim_inl, Sum.elim_inr, horth, reduceCtorEq, ite_false]
  · simp only [bV, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, ite_false]
    rw [polar_comm]
    exact horth _ _
  · simp only [bV, Sum.elim_inr, polar_incl_incl, polarDet_mVec hab, Sum.inr.injEq]

theorem polar_sum_smul_left {ι : Type} [Fintype ι] (c : ι → F) (e : ι → V) (w : V) :
    polar Q (∑ j, c j • e j) w = ∑ j, c j * polar Q (e j) w := by
  have h := map_sum ((polarBilin Q).flip w) (fun j => c j • e j) Finset.univ
  simp only [LinearMap.flip_apply, polarBilin_apply_apply, map_smul, smul_eq_mul] at h
  exact h

theorem linearIndependent_bV (h2 : (2 : F) ≠ 0) (hab : a ^ 2 + b ^ 2 = -1)
    (horth : ∀ X Y, polar Q (F₁.incl X) (F₃.incl Y) = 0) : LinearIndependent F (bV F₁ F₃ a b) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h := congrArg (fun v => polar Q v (bV F₁ F₃ a b i)) hc
  simp only [polar_sum_smul_left, polar_zero_left, polar_bV hab horth] at h
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  exact (mul_eq_zero.mp h).resolve_right h2

end Basis

section Ops

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {F₁ F₃ : OFrame Q} {a b : F}

@[expose] noncomputable def basisV (h2 : (2 : F) ≠ 0) (hab : a ^ 2 + b ^ 2 = -1)
    (horth : ∀ X Y, polar Q (F₁.incl X) (F₃.incl Y) = 0) (hdim : Module.finrank F V = 8) :
    Module.Basis (Fin 4 ⊕ Fin 4) F V :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_bV h2 hab horth)
    (by simp [hdim])

theorem ext_bV (h2 : (2 : F) ≠ 0) (hab : a ^ 2 + b ^ 2 = -1)
    (horth : ∀ X Y, polar Q (F₁.incl X) (F₃.incl Y) = 0) (hdim : Module.finrank F V = 8)
    {S T : V ≃ₗ[F] V} (h : ∀ i, S (bV F₁ F₃ a b i) = T (bV F₁ F₃ a b i)) : S = T := by
  refine LinearEquiv.toLinearMap_injective ((basisV h2 hab horth hdim).ext fun i => ?_)
  simpa [basisV] using h i

end Ops

section Tables

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {F₁ F₃ : OFrame Q} {a b : F}

theorem coords₃_incl₁ (horth : ∀ X Y, polar Q (F₁.incl X) (F₃.incl Y) = 0)
    (X : Matrix (Fin 2) (Fin 2) F) : F₃.coords (F₁.incl X) = 0 :=
  Frame.coords_incl_eq_zero_of_orth (F := F₃) (F' := F₁) horth X

theorem coords₁_incl₃ (horth : ∀ X Y, polar Q (F₁.incl X) (F₃.incl Y) = 0)
    (Y : Matrix (Fin 2) (Fin 2) F) : F₁.coords (F₃.incl Y) = 0 :=
  Frame.coords_incl_eq_zero_of_orth (F := F₁) (F' := F₃)
    (fun X Y => by rw [polar_comm]; exact horth Y X) Y

@[expose] def slB (F : Type) [Field F] : SL(2, F) := ⟨mB, det_mB⟩

@[expose] def slW {a b : F} (hab : a ^ 2 + b ^ 2 = -1) : SL(2, F) := ⟨mW a b, det_mW hab⟩

theorem La₁_inl (A : SL(2, F)) (j : Fin 4) :
    F₁.La A (bV F₁ F₃ a b (Sum.inl j)) = F₁.incl ((A : Matrix (Fin 2) (Fin 2) F) * mVec a b j) :=
  Frame.La_apply_incl _ _ _

theorem La₁_inr (horth : ∀ X Y, polar Q (F₁.incl X) (F₃.incl Y) = 0) (A : SL(2, F)) (j : Fin 4) :
    F₁.La A (bV F₁ F₃ a b (Sum.inr j)) = bV F₁ F₃ a b (Sum.inr j) :=
  Frame.La_apply_of_coords_eq_zero _ _ (coords₁_incl₃ horth _)

theorem La₃_inr (A : SL(2, F)) (j : Fin 4) :
    F₃.La A (bV F₁ F₃ a b (Sum.inr j)) = F₃.incl ((A : Matrix (Fin 2) (Fin 2) F) * mVec a b j) :=
  Frame.La_apply_incl _ _ _

theorem La₃_inl (horth : ∀ X Y, polar Q (F₁.incl X) (F₃.incl Y) = 0) (A : SL(2, F)) (j : Fin 4) :
    F₃.La A (bV F₁ F₃ a b (Sum.inl j)) = bV F₁ F₃ a b (Sum.inl j) :=
  Frame.La_apply_of_coords_eq_zero _ _ (coords₃_incl₁ horth _)

theorem bV_inl (j : Fin 4) : bV F₁ F₃ a b (Sum.inl j) = F₁.incl (mVec a b j) := rfl

theorem bV_inr (j : Fin 4) : bV F₁ F₃ a b (Sum.inr j) = F₃.incl (mVec a b j) := rfl

theorem swapLa_incl (F₀ : OFrame Q) (A : SL(2, F)) (Y : Matrix (Fin 2) (Fin 2) F) :
    F₀.swap.La A (F₀.incl Y) = F₀.incl (Y * sigmaLin (A : Matrix (Fin 2) (Fin 2) F)) := by
  rw [Frame.La_swap_apply, Frame.embLin_apply, Frame.coords_incl, ← map_add]
  simp only [LinearMap.mulRight_apply]
  congr 1
  abel

theorem swapLa₃_inl (horth : ∀ X Y, polar Q (F₁.incl X) (F₃.incl Y) = 0) (A : SL(2, F))
    (j : Fin 4) :
    F₃.swap.La A (bV F₁ F₃ a b (Sum.inl j)) = bV F₁ F₃ a b (Sum.inl j) := by
  rw [bV_inl, Frame.La_swap_apply, Frame.embLin_apply, coords₃_incl₁ horth]
  simp

theorem sigmaLin_mB : sigmaLin (K := F) (mB : Matrix (Fin 2) (Fin 2) F) = mB := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaLin_apply, mB]

@[expose] noncomputable def uB (F₃ : OFrame Q) : V ≃ₗ[F] V :=
  F₃.La (slB F) * F₃.swap.La (slB F)

theorem uB_inl (horth : ∀ X Y, polar Q (F₁.incl X) (F₃.incl Y) = 0) (j : Fin 4) :
    uB F₃ (bV F₁ F₃ a b (Sum.inl j)) = bV F₁ F₃ a b (Sum.inl j) := by
  rw [uB, LinearEquiv.mul_apply, swapLa₃_inl horth, La₃_inl horth]

theorem uB_inr (j : Fin 4) :
    uB F₃ (bV F₁ F₃ a b (Sum.inr j)) = sgnB F j • bV F₁ F₃ a b (Sum.inr j) := by
  rw [uB, LinearEquiv.mul_apply, bV_inr, swapLa_incl, Frame.La_apply_incl, ← map_smul]
  congr 1
  have : ((slB F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = mB := rfl
  rw [this, sigmaLin_mB, ← mul_assoc]
  exact mB_mul_mVec_mul_mB a b j

theorem La₁_slW {a b : F} (hab : a ^ 2 + b ^ 2 = -1) :
    F₁.La (slW hab) (bV F₁ F₃ a b (Sum.inl 0)) = bV F₁ F₃ a b (Sum.inl 2) ∧
      F₁.La (slW hab) (bV F₁ F₃ a b (Sum.inl 1)) = bV F₁ F₃ a b (Sum.inl 3) ∧
      F₁.La (slW hab) (bV F₁ F₃ a b (Sum.inl 2)) = -bV F₁ F₃ a b (Sum.inl 0) ∧
      F₁.La (slW hab) (bV F₁ F₃ a b (Sum.inl 3)) = -bV F₁ F₃ a b (Sum.inl 1) := by
  obtain ⟨h0, h1, h2, h3⟩ := mW_mul_mVec hab
  have hW : ((slW hab : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = mW a b := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [La₁_inl, hW, h0, bV_inl]
  · rw [La₁_inl, hW, h1, bV_inl]
  · rw [La₁_inl, hW, h2, bV_inl, map_neg]
  · rw [La₁_inl, hW, h3, bV_inl, map_neg]

theorem La₁_neg_one_inl (j : Fin 4) :
    F₁.La (-1) (bV F₁ F₃ a b (Sum.inl j)) = -bV F₁ F₃ a b (Sum.inl j) := by
  rw [La₁_inl, bV_inl, ← map_neg]
  congr 1
  simp

section Swap

variable {e f : V}

theorem Q_sub_of_orth (he : Q e = 1) (hf : Q f = 1) (hef : polar Q e f = 0) : Q (e - f) = 2 := by
  rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg Q, polar_neg_right, he, hf, hef]
  ring

noncomputable abbrev swapInv (h2 : (2 : F) ≠ 0) (he : Q e = 1) (hf : Q f = 1)
    (hef : polar Q e f = 0) : Invertible (Q (e - f)) :=
  invertibleOfNonzero (by rw [Q_sub_of_orth he hf hef]; exact h2)

@[expose] noncomputable def swapRefl (h2 : (2 : F) ≠ 0) (he : Q e = 1) (hf : Q f = 1)
    (hef : polar Q e f = 0) : V ≃ₗ[F] V :=
  letI := swapInv h2 he hf hef
  TauCeti.QuadraticMap.reflection Q (e - f)

theorem swapRefl_apply (h2 : (2 : F) ≠ 0) (he : Q e = 1) (hf : Q f = 1) (hef : polar Q e f = 0)
    (x : V) : swapRefl h2 he hf hef x = x - ((polar Q e x - polar Q f x) / 2) • (e - f) := by
  let _ := swapInv h2 he hf hef
  unfold swapRefl
  rw [TauCeti.QuadraticMap.reflection_apply_eq_sub_div, Q_sub_of_orth he hf hef, polar_sub_left]

theorem swapRefl_mem (h2 : (2 : F) ≠ 0) (he : Q e = 1) (hf : Q f = 1) (hef : polar Q e f = 0) :
    swapRefl h2 he hf hef ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  let _ := swapInv h2 he hf hef
  exact TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q (e - f)

theorem swapRefl_mul_self (h2 : (2 : F) ≠ 0) (he : Q e = 1) (hf : Q f = 1)
    (hef : polar Q e f = 0) : swapRefl h2 he hf hef * swapRefl h2 he hf hef = 1 := by
  let _ := swapInv h2 he hf hef
  exact TauCeti.QuadraticMap.reflection_mul_self Q (e - f)

theorem swapRefl_left (h2 : (2 : F) ≠ 0) (he : Q e = 1) (hf : Q f = 1) (hef : polar Q e f = 0) :
    swapRefl h2 he hf hef e = f := by
  rw [swapRefl_apply h2 he hf hef, polar_comm Q f e, hef, polar_self, he, sub_zero]
  simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  rw [div_self h2, one_smul, sub_sub_cancel]

theorem swapRefl_right (h2 : (2 : F) ≠ 0) (he : Q e = 1) (hf : Q f = 1) (hef : polar Q e f = 0) :
    swapRefl h2 he hf hef f = e := by
  rw [swapRefl_apply h2 he hf hef, hef, polar_self, hf, zero_sub]
  simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  rw [neg_div, div_self h2, neg_smul, one_smul, sub_neg_eq_add, add_sub_cancel]

theorem swapRefl_of_orth (h2 : (2 : F) ≠ 0) (he : Q e = 1) (hf : Q f = 1)
    (hef : polar Q e f = 0) {x : V} (hxe : polar Q e x = 0) (hxf : polar Q f x = 0) :
    swapRefl h2 he hf hef x = x := by
  rw [swapRefl_apply h2 he hf hef, hxe, hxf]
  simp

end Swap

section Rot

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {F₁ F₃ : OFrame Q} {a b : F}

theorem polar_bV_inl_inr (hab : a ^ 2 + b ^ 2 = -1)
    (horth : ∀ X Y, polar Q (F₁.incl X) (F₃.incl Y) = 0) (j k : Fin 4) :
    polar Q (bV F₁ F₃ a b (Sum.inl j)) (bV F₁ F₃ a b (Sum.inr k)) = 0 := by
  rw [polar_bV hab horth]
  simp

@[expose] noncomputable def refl₂ (h2 : (2 : F) ≠ 0) (hab : a ^ 2 + b ^ 2 = -1)
    (horth : ∀ X Y, polar Q (F₁.incl X) (F₃.incl Y) = 0) : V ≃ₗ[F] V :=
  swapRefl h2 (Q_bV hab (Sum.inl 2)) (Q_bV hab (Sum.inr 2)) (polar_bV_inl_inr hab horth 2 2)

@[expose] noncomputable def refl₃ (h2 : (2 : F) ≠ 0) (hab : a ^ 2 + b ^ 2 = -1)
    (horth : ∀ X Y, polar Q (F₁.incl X) (F₃.incl Y) = 0) : V ≃ₗ[F] V :=
  swapRefl h2 (Q_bV hab (Sum.inl 3)) (Q_bV hab (Sum.inr 3)) (polar_bV_inl_inr hab horth 3 3)

variable (h2 : (2 : F) ≠ 0) (hab : a ^ 2 + b ^ 2 = -1)
  (horth : ∀ X Y, polar Q (F₁.incl X) (F₃.incl Y) = 0)

theorem refl₂_of_ne {i : Fin 4 ⊕ Fin 4} (h1 : i ≠ Sum.inl 2) (h2' : i ≠ Sum.inr 2) :
    refl₂ h2 hab horth (bV F₁ F₃ a b i) = bV F₁ F₃ a b i := by
  refine swapRefl_of_orth h2 _ _ _ ?_ ?_
  · rw [polar_bV hab horth, ite_eq_right (Ne.symm h1)]
  · rw [polar_bV hab horth, ite_eq_right (Ne.symm h2')]

theorem refl₃_of_ne {i : Fin 4 ⊕ Fin 4} (h1 : i ≠ Sum.inl 3) (h2' : i ≠ Sum.inr 3) :
    refl₃ h2 hab horth (bV F₁ F₃ a b i) = bV F₁ F₃ a b i := by
  refine swapRefl_of_orth h2 _ _ _ ?_ ?_
  · rw [polar_bV hab horth, ite_eq_right (Ne.symm h1)]
  · rw [polar_bV hab horth, ite_eq_right (Ne.symm h2')]

theorem refl₂_inl : refl₂ h2 hab horth (bV F₁ F₃ a b (Sum.inl 2)) = bV F₁ F₃ a b (Sum.inr 2) :=
  swapRefl_left h2 _ _ _

theorem refl₂_inr : refl₂ h2 hab horth (bV F₁ F₃ a b (Sum.inr 2)) = bV F₁ F₃ a b (Sum.inl 2) :=
  swapRefl_right h2 _ _ _

theorem refl₃_inl : refl₃ h2 hab horth (bV F₁ F₃ a b (Sum.inl 3)) = bV F₁ F₃ a b (Sum.inr 3) :=
  swapRefl_left h2 _ _ _

theorem refl₃_inr : refl₃ h2 hab horth (bV F₁ F₃ a b (Sum.inr 3)) = bV F₁ F₃ a b (Sum.inl 3) :=
  swapRefl_right h2 _ _ _

@[expose] noncomputable def gRot : V ≃ₗ[F] V :=
  refl₂ h2 hab horth * refl₃ h2 hab horth

theorem gRot_mem : gRot h2 hab horth ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  (TauCeti.QuadraticMap.orthogonalGroup Q).mul_mem (swapRefl_mem h2 _ _ _) (swapRefl_mem h2 _ _ _)

@[expose] def gIdx : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4
  | Sum.inl j => if j = 2 then Sum.inr 2 else if j = 3 then Sum.inr 3 else Sum.inl j
  | Sum.inr j => if j = 2 then Sum.inl 2 else if j = 3 then Sum.inl 3 else Sum.inr j

theorem gRot_bV (i : Fin 4 ⊕ Fin 4) :
    gRot h2 hab horth (bV F₁ F₃ a b i) = bV F₁ F₃ a b (gIdx i) := by
  rcases i with j | j <;> fin_cases j
  · show gRot h2 hab horth (bV F₁ F₃ a b (Sum.inl 0)) = bV F₁ F₃ a b (gIdx (Sum.inl 0))
    rw [gRot, LinearEquiv.mul_apply, refl₃_of_ne h2 hab horth (by decide) (by decide),
      refl₂_of_ne h2 hab horth (by decide) (by decide)]
    simp [gIdx]
  · show gRot h2 hab horth (bV F₁ F₃ a b (Sum.inl 1)) = bV F₁ F₃ a b (gIdx (Sum.inl 1))
    rw [gRot, LinearEquiv.mul_apply, refl₃_of_ne h2 hab horth (by decide) (by decide),
      refl₂_of_ne h2 hab horth (by decide) (by decide)]
    simp [gIdx]
  · show gRot h2 hab horth (bV F₁ F₃ a b (Sum.inl 2)) = bV F₁ F₃ a b (gIdx (Sum.inl 2))
    rw [gRot, LinearEquiv.mul_apply, refl₃_of_ne h2 hab horth (by decide) (by decide), refl₂_inl]
    simp [gIdx]
  · show gRot h2 hab horth (bV F₁ F₃ a b (Sum.inl 3)) = bV F₁ F₃ a b (gIdx (Sum.inl 3))
    rw [gRot, LinearEquiv.mul_apply, refl₃_inl, refl₂_of_ne h2 hab horth (by decide) (by decide)]
    simp [gIdx]
  · show gRot h2 hab horth (bV F₁ F₃ a b (Sum.inr 0)) = bV F₁ F₃ a b (gIdx (Sum.inr 0))
    rw [gRot, LinearEquiv.mul_apply, refl₃_of_ne h2 hab horth (by decide) (by decide),
      refl₂_of_ne h2 hab horth (by decide) (by decide)]
    simp [gIdx]
  · show gRot h2 hab horth (bV F₁ F₃ a b (Sum.inr 1)) = bV F₁ F₃ a b (gIdx (Sum.inr 1))
    rw [gRot, LinearEquiv.mul_apply, refl₃_of_ne h2 hab horth (by decide) (by decide),
      refl₂_of_ne h2 hab horth (by decide) (by decide)]
    simp [gIdx]
  · show gRot h2 hab horth (bV F₁ F₃ a b (Sum.inr 2)) = bV F₁ F₃ a b (gIdx (Sum.inr 2))
    rw [gRot, LinearEquiv.mul_apply, refl₃_of_ne h2 hab horth (by decide) (by decide), refl₂_inr]
    simp [gIdx]
  · show gRot h2 hab horth (bV F₁ F₃ a b (Sum.inr 3)) = bV F₁ F₃ a b (gIdx (Sum.inr 3))
    rw [gRot, LinearEquiv.mul_apply, refl₃_inr, refl₂_of_ne h2 hab horth (by decide) (by decide)]
    simp [gIdx]

theorem gIdx_gIdx (i : Fin 4 ⊕ Fin 4) : gIdx (gIdx i) = i := by
  rcases i with j | j <;> fin_cases j <;> simp [gIdx]

theorem gRot_mul_self (hdim : Module.finrank F V = 8) :
    gRot h2 hab horth * gRot h2 hab horth = 1 := by
  refine ext_bV h2 hab horth hdim fun i => ?_
  rw [LinearEquiv.mul_apply, gRot_bV h2 hab horth, gRot_bV h2 hab horth, gIdx_gIdx]
  rfl

@[expose] def epsU (F : Type) [Field F] : Fin 4 ⊕ Fin 4 → F := Sum.elim (fun _ => 1) (sgnB F)

include horth in
theorem uB_bV (i : Fin 4 ⊕ Fin 4) :
    uB F₃ (bV F₁ F₃ a b i) = epsU F i • bV F₁ F₃ a b i := by
  rcases i with j | j
  · rw [uB_inl horth]
    simp [epsU]
  · rw [uB_inr]
    simp [epsU]

theorem epsU_gIdx (i : Fin 4 ⊕ Fin 4) : epsU F (gIdx i) = epsU F i := by
  rcases i with j | j <;> fin_cases j <;> simp [epsU, gIdx, sgnB]

theorem gRot_comm_uB (hdim : Module.finrank F V = 8) :
    gRot h2 hab horth * uB F₃ = uB F₃ * gRot h2 hab horth := by
  refine ext_bV h2 hab horth hdim fun i => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, uB_bV horth, map_smul,
    gRot_bV h2 hab horth, uB_bV horth, epsU_gIdx]

theorem gRot_inv (hdim : Module.finrank F V = 8) : (gRot h2 hab horth)⁻¹ = gRot h2 hab horth :=
  inv_eq_of_mul_eq_one_right (gRot_mul_self h2 hab horth hdim)

@[expose] noncomputable def xRot : V ≃ₗ[F] V :=
  gRot h2 hab horth * F₁.La (slW hab) * (gRot h2 hab horth)⁻¹

theorem xRot_apply (hdim : Module.finrank F V = 8) (x : V) :
    xRot h2 hab horth x = gRot h2 hab horth (F₁.La (slW hab) (gRot h2 hab horth x)) := by
  rw [xRot, gRot_inv h2 hab horth hdim]
  rfl

theorem gIdx_inl_zero : gIdx (Sum.inl 0) = Sum.inl 0 := by simp [gIdx]
theorem gIdx_inl_one : gIdx (Sum.inl 1) = Sum.inl 1 := by simp [gIdx]
theorem gIdx_inl_two : gIdx (Sum.inl 2) = Sum.inr 2 := by simp [gIdx]
theorem gIdx_inl_three : gIdx (Sum.inl 3) = Sum.inr 3 := by simp [gIdx]
theorem gIdx_inr_zero : gIdx (Sum.inr 0) = Sum.inr 0 := by simp [gIdx]
theorem gIdx_inr_one : gIdx (Sum.inr 1) = Sum.inr 1 := by simp [gIdx]
theorem gIdx_inr_two : gIdx (Sum.inr 2) = Sum.inl 2 := by simp [gIdx]
theorem gIdx_inr_three : gIdx (Sum.inr 3) = Sum.inl 3 := by simp [gIdx]

theorem xRot_values (hdim : Module.finrank F V = 8) :
    xRot h2 hab horth (bV F₁ F₃ a b (Sum.inl 0)) = bV F₁ F₃ a b (Sum.inr 2) ∧
    xRot h2 hab horth (bV F₁ F₃ a b (Sum.inl 1)) = bV F₁ F₃ a b (Sum.inr 3) ∧
    xRot h2 hab horth (bV F₁ F₃ a b (Sum.inl 2)) = bV F₁ F₃ a b (Sum.inl 2) ∧
    xRot h2 hab horth (bV F₁ F₃ a b (Sum.inl 3)) = bV F₁ F₃ a b (Sum.inl 3) ∧
    xRot h2 hab horth (bV F₁ F₃ a b (Sum.inr 0)) = bV F₁ F₃ a b (Sum.inr 0) ∧
    xRot h2 hab horth (bV F₁ F₃ a b (Sum.inr 1)) = bV F₁ F₃ a b (Sum.inr 1) ∧
    xRot h2 hab horth (bV F₁ F₃ a b (Sum.inr 2)) = -bV F₁ F₃ a b (Sum.inl 0) ∧
    xRot h2 hab horth (bV F₁ F₃ a b (Sum.inr 3)) = -bV F₁ F₃ a b (Sum.inl 1) := by
  obtain ⟨y0, y1, y2, y3⟩ := La₁_slW (F₁ := F₁) (F₃ := F₃) hab
  have yr := La₁_inr (F₁ := F₁) (F₃ := F₃) (a := a) (b := b) horth (slW hab)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [xRot_apply h2 hab horth hdim, gRot_bV h2 hab horth, gIdx_inl_zero, y0,
      gRot_bV h2 hab horth, gIdx_inl_two]
  · rw [xRot_apply h2 hab horth hdim, gRot_bV h2 hab horth, gIdx_inl_one, y1,
      gRot_bV h2 hab horth, gIdx_inl_three]
  · rw [xRot_apply h2 hab horth hdim, gRot_bV h2 hab horth, gIdx_inl_two, yr,
      gRot_bV h2 hab horth, gIdx_inr_two]
  · rw [xRot_apply h2 hab horth hdim, gRot_bV h2 hab horth, gIdx_inl_three, yr,
      gRot_bV h2 hab horth, gIdx_inr_three]
  · rw [xRot_apply h2 hab horth hdim, gRot_bV h2 hab horth, gIdx_inr_zero, yr,
      gRot_bV h2 hab horth, gIdx_inr_zero]
  · rw [xRot_apply h2 hab horth hdim, gRot_bV h2 hab horth, gIdx_inr_one, yr,
      gRot_bV h2 hab horth, gIdx_inr_one]
  · rw [xRot_apply h2 hab horth hdim, gRot_bV h2 hab horth, gIdx_inr_two, y2, map_neg,
      gRot_bV h2 hab horth, gIdx_inl_zero]
  · rw [xRot_apply h2 hab horth hdim, gRot_bV h2 hab horth, gIdx_inr_three, y3, map_neg,
      gRot_bV h2 hab horth, gIdx_inl_one]

@[expose] def eps₁ (F : Type) [Field F] : Fin 4 ⊕ Fin 4 → F := Sum.elim (fun _ => -1) (fun _ => 1)

include horth in
theorem La₁_neg_one_bV (i : Fin 4 ⊕ Fin 4) :
    F₁.La (-1) (bV F₁ F₃ a b i) = eps₁ F i • bV F₁ F₃ a b i := by
  rcases i with j | j
  · rw [La₁_neg_one_inl]
    simp [eps₁]
  · rw [La₁_inr horth]
    simp [eps₁]

@[expose] noncomputable def iX : V ≃ₗ[F] V :=
  xRot h2 hab horth * F₁.La (-1) * (xRot h2 hab horth)⁻¹

theorem iX_xRot (x : V) :
    iX h2 hab horth (xRot h2 hab horth x) = xRot h2 hab horth (F₁.La (-1) x) := by
  simp [iX]

theorem iX_bV_of {j k : Fin 4 ⊕ Fin 4} {s c : F} (hs : s ≠ 0)
    (hx : xRot h2 hab horth (bV F₁ F₃ a b j) = s • bV F₁ F₃ a b k)
    (hε : eps₁ F j = c) :
    iX h2 hab horth (bV F₁ F₃ a b k) = c • bV F₁ F₃ a b k := by
  have h := iX_xRot h2 hab horth (bV F₁ F₃ a b j)
  rw [hx, La₁_neg_one_bV horth, hε, map_smul, map_smul, hx, smul_comm c s] at h
  exact smul_right_injective V hs h

@[expose] def dX (F : Type) [Field F] : Fin 4 ⊕ Fin 4 → F :=
  Sum.elim (fun j => if j = 2 ∨ j = 3 then -1 else 1) (fun j => if j = 2 ∨ j = 3 then -1 else 1)

theorem iX_bV (hdim : Module.finrank F V = 8) (i : Fin 4 ⊕ Fin 4) :
    iX h2 hab horth (bV F₁ F₃ a b i) = dX F i • bV F₁ F₃ a b i := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := xRot_values (F₁ := F₁) (F₃ := F₃) h2 hab horth hdim
  have h1 : (1 : F) ≠ 0 := one_ne_zero
  have hm : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  rcases i with j | j <;> fin_cases j
  · show iX h2 hab horth (bV F₁ F₃ a b (Sum.inl 0)) = dX F (Sum.inl 0) • _
    have := iX_bV_of h2 hab horth (j := Sum.inr 2) (k := Sum.inl 0) (s := -1) (c := 1) hm
      (by rw [x6, neg_one_smul]) (by simp [eps₁])
    rw [this]
    simp [dX]
  · show iX h2 hab horth (bV F₁ F₃ a b (Sum.inl 1)) = dX F (Sum.inl 1) • _
    have := iX_bV_of h2 hab horth (j := Sum.inr 3) (k := Sum.inl 1) (s := -1) (c := 1) hm
      (by rw [x7, neg_one_smul]) (by simp [eps₁])
    rw [this]
    simp [dX]
  · show iX h2 hab horth (bV F₁ F₃ a b (Sum.inl 2)) = dX F (Sum.inl 2) • _
    have := iX_bV_of h2 hab horth (j := Sum.inl 2) (k := Sum.inl 2) (s := 1) (c := -1) h1
      (by rw [x2, one_smul]) (by simp [eps₁])
    rw [this]
    simp [dX]
  · show iX h2 hab horth (bV F₁ F₃ a b (Sum.inl 3)) = dX F (Sum.inl 3) • _
    have := iX_bV_of h2 hab horth (j := Sum.inl 3) (k := Sum.inl 3) (s := 1) (c := -1) h1
      (by rw [x3, one_smul]) (by simp [eps₁])
    rw [this]
    simp [dX]
  · show iX h2 hab horth (bV F₁ F₃ a b (Sum.inr 0)) = dX F (Sum.inr 0) • _
    have := iX_bV_of h2 hab horth (j := Sum.inr 0) (k := Sum.inr 0) (s := 1) (c := 1) h1
      (by rw [x4, one_smul]) (by simp [eps₁])
    rw [this]
    simp [dX]
  · show iX h2 hab horth (bV F₁ F₃ a b (Sum.inr 1)) = dX F (Sum.inr 1) • _
    have := iX_bV_of h2 hab horth (j := Sum.inr 1) (k := Sum.inr 1) (s := 1) (c := 1) h1
      (by rw [x5, one_smul]) (by simp [eps₁])
    rw [this]
    simp [dX]
  · show iX h2 hab horth (bV F₁ F₃ a b (Sum.inr 2)) = dX F (Sum.inr 2) • _
    have := iX_bV_of h2 hab horth (j := Sum.inl 0) (k := Sum.inr 2) (s := 1) (c := -1) h1
      (by rw [x0, one_smul]) (by simp [eps₁])
    rw [this]
    simp [dX]
  · show iX h2 hab horth (bV F₁ F₃ a b (Sum.inr 3)) = dX F (Sum.inr 3) • _
    have := iX_bV_of h2 hab horth (j := Sum.inl 1) (k := Sum.inr 3) (s := 1) (c := -1) h1
      (by rw [x1, one_smul]) (by simp [eps₁])
    rw [this]
    simp [dX]

theorem bV_ne_zero (hab : a ^ 2 + b ^ 2 = -1) (i : Fin 4 ⊕ Fin 4) :
    bV F₁ F₃ a b i ≠ 0 := by
  intro h
  have := Q_bV (F₁ := F₁) (F₃ := F₃) hab i
  rw [h, QuadraticMap.map_zero] at this
  exact zero_ne_one this

theorem eq_zero_of_neg_eq_self (h2 : (2 : F) ≠ 0) {v : V} (h : -v = v) : v = 0 := by
  have : (2 : F) • v = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h]
    exact neg_add_cancel v
  exact (smul_eq_zero.mp this).resolve_left h2

theorem iX_comm_i₁ (hdim : Module.finrank F V = 8) :
    iX h2 hab horth * F₁.La (-1) = F₁.La (-1) * iX h2 hab horth := by
  refine ext_bV h2 hab horth hdim fun i => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, La₁_neg_one_bV horth, map_smul,
    iX_bV h2 hab horth hdim, map_smul, La₁_neg_one_bV horth, smul_smul, smul_smul, mul_comm]

theorem iX_mul_i₁_ne_one (hdim : Module.finrank F V = 8) :
    iX h2 hab horth * F₁.La (-1) ≠ 1 := by
  intro h
  have h0 : (iX h2 hab horth * F₁.La (-1)) (bV F₁ F₃ a b (Sum.inl 0)) =
      bV F₁ F₃ a b (Sum.inl 0) := by
    rw [h]
    rfl
  rw [LinearEquiv.mul_apply, La₁_neg_one_bV horth, map_smul, iX_bV h2 hab horth hdim] at h0
  simp only [eps₁, dX, Sum.elim_inl] at h0
  simp at h0
  exact bV_ne_zero hab (Sum.inl 0) (eq_zero_of_neg_eq_self h2 h0)

theorem iX_mul_i₁_ne_neg (hdim : Module.finrank F V = 8) :
    iX h2 hab horth * F₁.La (-1) ≠ LinearEquiv.neg F := by
  intro h
  have h0 := congrArg (fun T : V ≃ₗ[F] V => T (bV F₁ F₃ a b (Sum.inl 2))) h
  simp only [LinearEquiv.mul_apply, LinearEquiv.neg_apply] at h0
  rw [La₁_neg_one_bV horth, map_smul, iX_bV h2 hab horth hdim] at h0
  simp only [eps₁, dX, Sum.elim_inl] at h0
  simp at h0
  exact bV_ne_zero hab (Sum.inl 2) (eq_zero_of_neg_eq_self h2 h0.symm)

end Rot

end Tables

end CFSG.ClassicalInvolution.RouteD.Exotic
