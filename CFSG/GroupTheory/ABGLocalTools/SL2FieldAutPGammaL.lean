module

public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutSemilinear
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2

public section

namespace CFSG.ABGLocalTools

open Matrix CFSG.GorensteinWalter

universe u

section PSL

variable {F : Type u} [Field F]

@[expose] noncomputable def psl2MulAutOf (α : MulAut (SpecialLinearGroup (Fin 2) F)) :
    MulAut (PSL2 F) :=
  QuotientGroup.congr (Subgroup.center _) (Subgroup.center _) α (Subgroup.map_center_eq α)

theorem psl2MulAutOf_mk (α : MulAut (SpecialLinearGroup (Fin 2) F))
    (b : SpecialLinearGroup (Fin 2) F) :
    psl2MulAutOf α (QuotientGroup.mk' _ b) = QuotientGroup.mk' _ (α b) := rfl

theorem psl2MulAutOf_pow_mk (α : MulAut (SpecialLinearGroup (Fin 2) F)) (k : ℕ)
    (b : SpecialLinearGroup (Fin 2) F) :
    (psl2MulAutOf α ^ k) (QuotientGroup.mk' _ b) = QuotientGroup.mk' _ ((α ^ k) b) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih, psl2MulAutOf_mk, pow_succ', MulAut.mul_apply]

theorem psl2MulAutOf_pow_eq_one {α : MulAut (SpecialLinearGroup (Fin 2) F)} {p : ℕ}
    (hα : α ^ p = 1) : psl2MulAutOf α ^ p = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with | H b => ?_
  rw [MulAut.one_apply]
  change (psl2MulAutOf α ^ p) (QuotientGroup.mk' _ b) = QuotientGroup.mk' _ b
  rw [psl2MulAutOf_pow_mk, hα, MulAut.one_apply]

end PSL

section PGammaL

variable {F : Type u} [Field F]

theorem pGammaL2_pow_right (γ : PGammaL2 F) (k : ℕ) : (γ ^ k).right = γ.right ^ k := by
  rw [← SemidirectProduct.rightHom_eq_right, map_pow, SemidirectProduct.rightHom_eq_right]

theorem pGammaL2_pow_left (γ : PGammaL2 F) (G : GL (Fin 2) F)
    (hG : ProjGenLinGroup.mk G = γ.left) (k : ℕ) :
    (γ ^ k).left = ProjGenLinGroup.mk (glNorm γ.right G k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, SemidirectProduct.mul_left, ih, pGammaL2_pow_right, ← hG, glNorm_succ,
      map_mul, pgl2FieldAut_apply]
    congr 1
    exact pgl2RingEquiv_mk (γ.right ^ k) G

end PGammaL

section Lift

variable {F : Type u} [Field F] [Finite F]

theorem coe_mulAut_eq_smul_conj (hK : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (α : MulAut (SpecialLinearGroup (Fin 2) F)) (γ : PGammaL2 F)
    (hγ : pGammaL2ToMulAutPSL2 F hK hcard γ = psl2MulAutOf α) (G : GL (Fin 2) F)
    (hG : ProjGenLinGroup.mk G = γ.left) (b : SpecialLinearGroup (Fin 2) F) :
    ∃ u : F, u ≠ 0 ∧ ((α b : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      u • ((G : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F).map γ.right *
        ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := by
  have h1 : ProjectiveSpecialLinearGroup.toPGL (psl2MulAutOf α (QuotientGroup.mk' _ b)) =
      ProjectiveSpecialLinearGroup.toPGL (pGammaL2ToMulAutPSL2 F hK hcard γ
        (QuotientGroup.mk' _ b)) := by
    rw [hγ]
  have hdecomp : γ = SemidirectProduct.inl γ.left * SemidirectProduct.inr γ.right :=
    (SemidirectProduct.inl_left_mul_inr_right γ).symm
  rw [psl2MulAutOf_mk, hdecomp, map_mul, pGammaL2ToMulAutPSL2_inl, pGammaL2ToMulAutPSL2_inr,
    MulAut.mul_apply, toPGL_pgl2InnerAutPSL2_apply, psl2FieldAut_toPGL] at h1
  change ProjGenLinGroup.mk (SpecialLinearGroup.toGL (α b)) =
    γ.left * (pgl2FieldAut F) γ.right (ProjGenLinGroup.mk (SpecialLinearGroup.toGL b)) *
      γ.left⁻¹ at h1
  rw [pgl2FieldAut_apply, ← hG] at h1
  change ProjGenLinGroup.mk (SpecialLinearGroup.toGL (α b)) =
    ProjGenLinGroup.mk G * pgl2RingEquiv γ.right
      (QuotientGroup.mk' _ (SpecialLinearGroup.toGL b)) * (ProjGenLinGroup.mk G)⁻¹ at h1
  rw [pgl2RingEquiv_mk] at h1
  change ProjGenLinGroup.mk (SpecialLinearGroup.toGL (α b)) =
    ProjGenLinGroup.mk G * ProjGenLinGroup.mk
      (GeneralLinearGroup.map γ.right.toRingHom (SpecialLinearGroup.toGL b)) *
        (ProjGenLinGroup.mk G)⁻¹ at h1
  rw [← map_mul, ← map_inv, ← map_mul, ProjGenLinGroup.mk_eq_mk_iff] at h1
  obtain ⟨w, hw⟩ := h1
  have hw' := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F)) hw
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at hw'
  have hmap : ((GeneralLinearGroup.map γ.right.toRingHom (SpecialLinearGroup.toGL b) :
      GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = (b : Matrix (Fin 2) (Fin 2) F).map γ.right :=
    rfl
  have hαb : ((SpecialLinearGroup.toGL (α b) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((α b : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := rfl
  rw [hmap, hαb] at hw'
  refine ⟨(w : F)⁻¹, inv_ne_zero w.ne_zero, ?_⟩
  rw [← hw', Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one,
    smul_smul, inv_mul_cancel₀ w.ne_zero, one_smul]

end Lift

end CFSG.ABGLocalTools
