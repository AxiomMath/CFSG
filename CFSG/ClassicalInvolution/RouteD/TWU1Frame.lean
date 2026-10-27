module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15Frame
public import CFSG.ClassicalInvolution.RouteD.GapsFrChain

public section

namespace CFSG.ClassicalInvolution.RouteD.TWU

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.RouteD.Gaps
open scoped MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

@[expose] def diagI (i : F) (hi : i * i = -1) : SL(2, F) :=
  ⟨!![i, 0; 0, -i], by
    rw [Matrix.det_fin_two_of]
    linear_combination -hi⟩

@[expose] def diagM (i : F) (hi : i * i = -1) : SL(2, F) :=
  ⟨!![-i, 0; 0, i], by
    rw [Matrix.det_fin_two_of]
    linear_combination -hi⟩

theorem coe_diagI (i : F) (hi : i * i = -1) :
    (diagI i hi : Matrix (Fin 2) (Fin 2) F) = !![i, 0; 0, -i] := rfl

theorem coe_diagM (i : F) (hi : i * i = -1) :
    (diagM i hi : Matrix (Fin 2) (Fin 2) F) = !![-i, 0; 0, i] := rfl

theorem diagI_mul_self (i : F) (hi : i * i = -1) :
    (diagI i hi : Matrix (Fin 2) (Fin 2) F) * diagI i hi = -1 := by
  rw [coe_diagI]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hi]

theorem diagM_mul_self (i : F) (hi : i * i = -1) :
    (diagM i hi : Matrix (Fin 2) (Fin 2) F) * diagM i hi = -1 := by
  rw [coe_diagM]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hi]

theorem twinInv_apply (fr : OFrame Q) (A A' : SL(2, F)) (x : V) :
    twinInv fr A A' x = x + fr.incl ((A : Matrix (Fin 2) (Fin 2) F) * fr.coords x *
      sigmaLin (A' : Matrix (Fin 2) (Fin 2) F) - fr.coords x) := by
  obtain ⟨X, r, hr, rfl⟩ : ∃ X r, r ∈ fr.perp ∧ x = fr.incl X + r :=
    ⟨fr.coords x, x - fr.incl (fr.coords x), (decomp_span_perp fr x).2,
      (decomp_span_perp fr x).1⟩
  have hc : fr.coords (fr.incl X + r) = X := by
    rw [map_add, Frame.coords_incl, (Frame.mem_perp_iff fr).mp hr, add_zero]
  rw [hc, map_add, twinInv_incl, twinInv_perp fr A A' hr, map_sub]
  abel

@[expose] def projPair (P : HypPair Q) (x : V) : V := polar Q x P.f • P.e + polar Q x P.e • P.f

theorem twinInv_diagI_diagI (fr : OFrame Q) (i : F) (hi : i * i = -1) (x : V) :
    twinInv fr (diagI i hi) (diagI i hi) x = x - (2 : F) • projPair fr.P x := by
  have h : ∀ a : F, i * a * i = -a := fun a => by linear_combination a * hi
  rw [twinInv_apply]
  simp [Frame.incl_apply, Frame.coords_apply, coe_diagI, sigmaLin_apply, projPair, h]
  module

theorem twinInv_diagI_diagM (fr : OFrame Q) (i : F) (hi : i * i = -1) (x : V) :
    twinInv fr (diagI i hi) (diagM i hi) x = x - (2 : F) • projPair fr.P' x := by
  have h : ∀ a : F, i * a * i = -a := fun a => by linear_combination a * hi
  have h' : ∀ a : F, i * a * -i = a := fun a => by linear_combination (-a) * hi
  rw [twinInv_apply]
  simp [Frame.incl_apply, Frame.coords_apply, coe_diagI, coe_diagM, sigmaLin_apply, projPair, h,
    h']
  module

theorem projPair_sub (P : HypPair Q) (x y : V) :
    projPair P (x - y) = projPair P x - projPair P y := by
  simp only [projPair, polar_sub_left]
  module

theorem projPair_smul (P : HypPair Q) (a : F) (x : V) :
    projPair P (a • x) = a • projPair P x := by
  simp only [projPair, polar_smul_left, smul_eq_mul]
  module

theorem projPair_swapPair (P : HypPair Q) (x : V) : projPair (swapPair P) x = projPair P x := by
  simp only [projPair, swapPair]
  abel

theorem projPair_projPair_of_orth {P P' : HypPair Q} (h : P.Orth P') (x : V) :
    projPair P (projPair P' x) = 0 := by
  simp only [projPair, polar_add_left, polar_smul_left, smul_eq_mul]
  rw [polar_comm Q P'.e P.f, polar_comm Q P'.f P.f, polar_comm Q P'.e P.e, polar_comm Q P'.f P.e,
    h.fe, h.ff, h.ee, h.ef]
  simp

theorem La_neg_one_apply_proj (fr : OFrame Q) (x : V) :
    fr.La (-1) x = x - (2 : F) • (projPair fr.P x + projPair fr.P' x) := by
  rw [Frame.La_neg_one_apply]
  simp [Frame.incl_apply, Frame.coords_apply, projPair]
  module

theorem La_neg_one_eq_twinInv_mul (i : F) (hi : i * i = -1) (c₀ c₁ c₂ c₃ : HypPair Q)
    (o01 : c₀.Orth (swapPair c₁)) (o12 : c₁.Orth (swapPair c₂)) (o23 : c₂.Orth (swapPair c₃))
    (h12 : c₁.Orth c₂) :
    (mkFrame c₁ (swapPair c₂) o12).La (-1) =
      twinInv (mkFrame c₀ (swapPair c₁) o01) (diagI i hi) (diagM i hi) *
        twinInv (mkFrame c₂ (swapPair c₃) o23) (diagI i hi) (diagI i hi) := by
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, twinInv_diagI_diagI, twinInv_diagI_diagM, La_neg_one_apply_proj]
  simp only [mkFrame, projPair_swapPair, projPair_sub, projPair_smul,
    projPair_projPair_of_orth h12]
  module

end CFSG.ClassicalInvolution.RouteD.TWU
