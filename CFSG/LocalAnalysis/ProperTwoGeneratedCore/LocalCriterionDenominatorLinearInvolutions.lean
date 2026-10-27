module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCentralizers
public import TauCeti.LinearAlgebra.Matrix.Commute
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MatrixFieldTransport

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open Matrix CFSG.Open CFSG.ShultStronglyClosedTI

section CharacteristicTwo

variable {K : Type*} [Field K] [CharP K 2]

theorem sl2_equal_diagonal_inv (A : Matrix.SpecialLinearGroup (Fin 2) K)
    (hdiag : A 0 0 = A 1 1) : A⁻¹ = A := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq, hdiag]

omit [CharP K 2] in
theorem sl2_involution_equal_diagonal (A : Matrix.SpecialLinearGroup (Fin 2) K)
    (hA : orderOf A = 2) : A 0 0 = A 1 1 := by
  have h := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 2) K => B 0 0)
    (inv_eq_self_of_orderOf_eq_two hA)
  simpa only [Matrix.SpecialLinearGroup.SL2_inv_expl, Matrix.SpecialLinearGroup.coe_mk,
    Matrix.cons_val_zero] using h.symm

theorem sl2_scalar_eq_one (A : Matrix.SpecialLinearGroup (Fin 2) K)
    (hscalar : (A : Matrix (Fin 2) (Fin 2) K) ∈ Set.range (Matrix.scalar (Fin 2))) :
    A = 1 := by
  obtain ⟨c, hc⟩ := hscalar
  have hdet : c ^ 2 = 1 := by
    have h := A.property
    rw [← hc] at h
    simpa only [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two, pow_two] using h
  have hc1 : c = 1 := CharTwo.sq_injective (hdet.trans (one_pow 2).symm)
  apply Subtype.ext
  rw [← hc, hc1, Matrix.SpecialLinearGroup.coe_one]
  simp only [Matrix.scalar_apply, Matrix.diagonal_one]

theorem sl2_charTwo_center_eq_bot :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  apply le_antisymm
  · intro A hA
    apply Subgroup.mem_bot.mpr
    obtain ⟨c, _, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    exact sl2_scalar_eq_one A ⟨c, hc⟩
  · exact bot_le

@[expose] def psl2CharTwoEquivSL :
    ProjectiveSpecialLinearGroup (Fin 2) K ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
  (QuotientGroup.quotientMulEquivOfEq sl2_charTwo_center_eq_bot).trans
    QuotientGroup.quotientBot

theorem sl2_involution_centralizer_square (A : Matrix.SpecialLinearGroup (Fin 2) K)
    (hA : orderOf A = 2)
    (B : Subgroup.centralizer ({A} : Set (Matrix.SpecialLinearGroup (Fin 2) K))) :
    B ^ 2 = 1 := by
  have hscalar : (A : Matrix (Fin 2) (Fin 2) K) ∉ Set.range (Matrix.scalar (Fin 2)) := by
    intro h
    have hA1 := sl2_scalar_eq_one A h
    rw [hA1, orderOf_one] at hA
    omega
  have hcomm : Commute (A : Matrix (Fin 2) (Fin 2) K)
      (B.val : Matrix (Fin 2) (Fin 2) K) := by
    change (A : Matrix (Fin 2) (Fin 2) K) * B.val = B.val * A
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using congrArg
      (fun C : Matrix.SpecialLinearGroup (Fin 2) K => (C : Matrix (Fin 2) (Fin 2) K))
      (Subgroup.mem_centralizer_singleton_iff.mp B.property).symm
  obtain ⟨a, b, hab⟩ := (TauCeti.commute_fin_two_iff hscalar).mp hcomm
  have hdiag : B.val 0 0 = B.val 1 1 := by
    have h00 := congrArg (fun C : Matrix (Fin 2) (Fin 2) K => C 0 0) hab
    have h11 := congrArg (fun C : Matrix (Fin 2) (Fin 2) K => C 1 1) hab
    simp only [Matrix.add_apply, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Matrix.smul_apply, smul_eq_mul] at h00 h11
    rw [h00, h11, sl2_involution_equal_diagonal A hA]
  apply Subtype.ext
  change B.val ^ 2 = 1
  calc
    B.val ^ 2 = B.val * B.val := pow_two _
    _ = B.val⁻¹ * B.val := congrArg (fun C : Matrix.SpecialLinearGroup (Fin 2) K => C * B.val)
      (sl2_equal_diagonal_inv B.val hdiag).symm
    _ = 1 := inv_mul_cancel _

theorem sl2_involution_centralizer_isPGroup (A : Matrix.SpecialLinearGroup (Fin 2) K)
    (hA : orderOf A = 2) :
    IsPGroup 2 (Subgroup.centralizer ({A} : Set (Matrix.SpecialLinearGroup (Fin 2) K))) := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro B
  exact ⟨1, by simpa only [pow_one] using sl2_involution_centralizer_square A hA B⟩

theorem psl2_charTwo_involution_centralizer_isPGroup
    (A : ProjectiveSpecialLinearGroup (Fin 2) K) (hA : orderOf A = 2) :
    IsPGroup 2 (Subgroup.centralizer ({A} : Set (ProjectiveSpecialLinearGroup (Fin 2) K))) := by
  let e := psl2CharTwoEquivSL (K := K)
  have heA : orderOf (e A) = 2 := (orderOf_injective e.toMonoidHom e.injective A).trans hA
  exact (sl2_involution_centralizer_isPGroup (e A) heA).of_equiv
    (elementCentralizerEquiv e A).symm

end CharacteristicTwo

theorem linear_model_involution_centralizers_two {G : Type*} [Group G]
    {K : Type} [Field K] [Finite K] (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = 2 ^ f) (e : G ≃* GLAProj (GLASLGroup (Fin 2) K)) :
    ∀ t : G, orderOf t = 2 → IsPGroup 2 (Subgroup.centralizer ({t} : Set G)) := by
  let E := e.trans (glaSL2EquivNative f hf hcard)
  intro t ht
  have hEt : orderOf (E t) = 2 := (orderOf_injective E.toMonoidHom E.injective t).trans ht
  exact (psl2_charTwo_involution_centralizer_isPGroup (E t) hEt).of_equiv
    (elementCentralizerEquiv E t).symm

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
