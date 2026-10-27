module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aNodes
public import CFSG.LieType.SpecialLinear.BorelStd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearSemilinearAction

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL

open scoped MatrixGroups Matrix

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.K1

theorem exists_frobPow_eq {F : Type} [Field F] [Fintype F] [CharP F 2] (σ : F ≃+* F) :
    ∃ j : ℕ, ∀ x, σ x = x ^ 2 ^ j := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hfix : ∀ r : ZMod 2, σ (algebraMap (ZMod 2) F r) = algebraMap (ZMod 2) F r := by
    intro r
    change σ (ZMod.cast (n := 2) r) = ZMod.cast (n := 2) r
    exact map_natCast σ r.val
  let g : F ≃ₐ[ZMod 2] F := AlgEquiv.ofRingEquiv (f := σ) hfix
  obtain ⟨j, hj⟩ := FiniteField.exists_forall_apply_eq_pow (k := ZMod 2) (p := 2) F g
  refine ⟨j, fun x => ?_⟩
  have h2 : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  simpa [g, h2] using hj x

theorem frobPow_eq_iterate {F : Type} [Field F] [CharP F 2] (j : ℕ) (x : SL(3, F)) :
    CFSG.QuasithinUnique.Setup.X7a.frobPow F j x =
      (CFSG.QuasithinUnique.Setup.X7a.frobSL F)^[j] x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show CFSG.QuasithinUnique.Setup.X7a.frobSL F
        (CFSG.QuasithinUnique.Setup.X7a.frobPow F j x) = _
    rw [ih, Function.iterate_succ_apply']

theorem stdAut_one_apply_eq {F : Type} [Field F] [CharP F 2]
    (A : GL (Fin 3) F) (σ : F ≃+* F) {j : ℕ} (hσ : ∀ x, σ x = x ^ 2 ^ j)
    (x : SL(3, F)) :
    CFSG.QuasithinUnique.K1.stdAut A σ 1 x =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A
        (CFSG.QuasithinUnique.Setup.X7a.tauSL F
          (CFSG.QuasithinUnique.Setup.X7a.frobPow F j x)) := by
  apply Subtype.ext
  rw [coe_stdAut_one, coe_slConjugation,
    CFSG.QuasithinUnique.Setup.X7a.tauSL_coe, CFSG.QuasithinUnique.Setup.X7a.trInvMat]
  have hmid : (((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ).map σ =
      ((((CFSG.QuasithinUnique.Setup.X7a.frobPow F j x)⁻¹ : SL(3, F)) :
        Matrix (Fin 3) (Fin 3) F)ᵀ) := by
    rw [← map_inv (CFSG.QuasithinUnique.Setup.X7a.frobPow F j) x, frobPow_eq_iterate,
      CFSG.QuasithinUnique.Setup.X7a.frobSL_iterate_coe, Matrix.transpose_map]
    congr 1
    ext i k
    exact hσ _
  rw [hmid]

theorem borelStd_one_eq_stdAut (n : ℕ) (F : Type) [Field F] (A : GL (Fin n) F)
    (σ : F ≃+* F) :
    CFSG.LieType.SpecialLinear.borelStd n F A σ 1 =
      CFSG.QuasithinUnique.K1.stdAut (A * CFSG.LieType.SpecialLinear.revGL n F) σ 1 := by
  have hw : CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin n) F σ
      (CFSG.LieType.SpecialLinear.revGL n F) = CFSG.LieType.SpecialLinear.revGL n F := by
    apply GeneralLinearGroup.ext
    intro i j
    change (CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv
      (Fin n) σ (CFSG.LieType.SpecialLinear.revGL n F) : GL (Fin n) F) i j = _
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv_entry,
      CFSG.LieType.SpecialLinear.coe_revGL, permMatrix_apply]
    split_ifs <;> simp
  have hmul := CFSG.ComponentClassification.CatalogueBLinearSemilinear.slSemilinearAction_mul
    n F A (CFSG.LieType.SpecialLinear.revGL n F) σ (RingEquiv.refl F)
  simp only [CFSG.ComponentClassification.CatalogueBLinearSemilinear.slSemilinearAction]
      at hmul
  have hrefl : (RingEquiv.refl F : F ≃+* F) = 1 := rfl
  rw [hrefl] at hmul
  rw [hw, map_one, mul_one, mul_one] at hmul
  simp only [CFSG.LieType.SpecialLinear.borelStd, CFSG.LieType.SpecialLinear.borelGraph,
    CFSG.QuasithinUnique.K1.stdAut, pow_one, pow_zero, mul_one]
  calc
    (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F A *
          CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin n) F σ) *
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F
            (CFSG.LieType.SpecialLinear.revGL n F) *
          CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut n F) =
        ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F A *
            CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut
              (Fin n) F σ) *
          CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F
            (CFSG.LieType.SpecialLinear.revGL n F)) *
          CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut n F := by
          group
    _ = (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F
            (A * CFSG.LieType.SpecialLinear.revGL n F) *
          CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin n) F σ) *
          CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut n F := by
          rw [hmul]

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL
