module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFieldArith
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUnitaryAut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitary
  CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {p f : ℕ} {F : Type} [Field F]

theorem eq_of_descend_eq (h : UnitaryFieldData p f F) (hq : 2 < p ^ f)
    {θ θ' : MulAut (unitarySU p f F 3)}
    (hd : MulAut.congr (suCenterEquiv h hq) (centerDescend _ θ) =
      MulAut.congr (suCenterEquiv h hq) (centerDescend _ θ')) : θ = θ' := by
  have hdesc : centerDescend _ θ = centerDescend _ θ' :=
    (MulAut.congr (suCenterEquiv h hq)).injective hd
  have : Group.IsPerfect (unitarySU p f F 3) := isPerfect_unitarySU_three h hq
  have hτ : θ * θ'⁻¹ = 1 := by
    apply eq_one_of_forall_mul_inv_mem_center
    intro s
    have h1 := congrArg (fun τ : MulAut (unitarySU p f F 3 ⧸ Subgroup.center _) =>
      τ (((θ'⁻¹ s : unitarySU p f F 3)) : unitarySU p f F 3 ⧸ Subgroup.center _)) hdesc
    simp only [centerDescend_mk] at h1
    rw [MulAut.apply_inv_self] at h1
    exact QuotientGroup.eq.1 h1.symm
  exact mul_inv_eq_one.1 hτ

theorem descend_suConj (h : UnitaryFieldData p f F) (hq : 2 < p ^ f) (B : unitaryIsom3 h) :
    MulAut.congr (suCenterEquiv h hq) (centerDescend _ (suConj h B)) = psuConj h B := by
  ext y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  rfl

theorem descend_suField (h : UnitaryFieldData p f F) (hq : 2 < p ^ f) (σ : F ≃+* F) :
    MulAut.congr (suCenterEquiv h hq) (centerDescend _ (suField h σ)) = psuField h σ := by
  ext y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  rfl

theorem exists_suConj_or_conj_suField (h : UnitaryFieldData p f F) (hq : 2 < p ^ f)
    {θ : MulAut (unitarySU p f F 3)} (hθ : θ ^ 3 = 1) :
    (∃ B : unitaryIsom3 h, θ = suConj h B) ∨
      ∃ (σ : F ≃+* F) (H : unitaryIsom3 h), orderOf σ = 3 ∧
        θ = suConj h H * suField h σ * (suConj h H)⁻¹ := by
  set α : MulAut (unitaryPSU h 3) :=
    MulAut.congr (suCenterEquiv h hq) (centerDescend _ θ) with hα
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, ← map_pow, hθ, map_one, map_one]
  by_cases hD : α ∈ (psuConj h).range
  · left
    obtain ⟨B, hB⟩ := hD
    exact ⟨B, eq_of_descend_eq h hq (by rw [descend_suConj, hB])⟩
  · right
    obtain ⟨σ, hσ, H, hαH⟩ := unitary_order_three_field_descent hq α hα3 hD
    refine ⟨σ, H, hσ, eq_of_descend_eq h hq ?_⟩
    rw [map_mul, map_mul, map_inv, map_inv, map_mul, map_mul, descend_suConj, descend_suField]
    exact hαH

theorem suField_mul_suConj_mul_inv (h : UnitaryFieldData p f F) (σ : F ≃+* F)
    (B : unitaryIsom3 h) :
    suField h σ * suConj h B * (suField h σ)⁻¹ =
      suConj h ⟨glAut σ B, glAut_mem_unitaryIsom3 σ B.2⟩ := by
  ext1 s
  apply Subtype.ext
  rw [← map_inv, MulAut.mul_apply, MulAut.mul_apply, coe_suField, coe_suConj, coe_suField,
    coe_suConj, map_mul, map_mul, map_inv, ← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  rfl

theorem exists_scalar_of_comm (h : UnitaryFieldData p f F) {B : unitaryIsom3 h} {τ : F ≃+* F}
    (hcomm : suConj h B * suField h τ = suField h τ * suConj h B) :
    ∃ c : Fˣ, h.norm (c : F) = 1 ∧
      (glAut τ (B : GL (Fin 3) F) : GL (Fin 3) F) =
        (B : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c := by
  have h1 : suField h τ * suConj h B * (suField h τ)⁻¹ = suConj h B := by
    rw [← hcomm]
    group
  rw [suField_mul_suConj_mul_inv] at h1
  have h2 : suConj h (B⁻¹ * ⟨glAut τ B, glAut_mem_unitaryIsom3 τ B.2⟩) = 1 := by
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  obtain ⟨c, hc, hcB⟩ := exists_scalar_of_suConj_eq_one h h2
  refine ⟨c, hc, ?_⟩
  have h3 : (B : GL (Fin 3) F)⁻¹ * glAut τ (B : GL (Fin 3) F) =
      GeneralLinearGroup.scalar (Fin 3) c := hcB
  rw [← h3]
  group

variable [Finite F]

theorem exists_suConj_mul_pow (h : UnitaryFieldData p f F) (hq : 2 < p ^ f) {τ : F ≃+* F}
    (hτ : orderOf τ = 3) {θ : MulAut (unitarySU p f F 3)} (hθ : θ ^ 3 = 1) :
    ∃ (m : ℕ) (B : unitaryIsom3 h), θ * suField h τ ^ m = suConj h B := by
  rcases exists_suConj_or_conj_suField h hq hθ with ⟨B, hB⟩ | ⟨σ, H, hσ, hθσ⟩
  · exact ⟨0, B, by rw [pow_zero, mul_one]; exact hB⟩
  · obtain ⟨hcyc, hfin⟩ := isCyclic_ringEquiv F
    have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
    obtain ⟨j, hj, hσj⟩ := exists_pow_eq_of_pow_three_eq_one hτ hσ3
    have hτ3 : τ ^ 3 = 1 := by rw [← hτ]; exact pow_orderOf_eq_one τ
    have hone : σ * τ ^ (3 - j) = 1 := by
      rw [hσj, ← pow_add, show j + (3 - j) = 3 by omega, hτ3]
    have hV := suField_mul_suConj_mul_inv h σ H
    have hθ' : θ = suConj h (H * (⟨glAut σ H, glAut_mem_unitaryIsom3 σ H.2⟩ : unitaryIsom3 h)⁻¹) *
        suField h σ := by
      rw [map_mul, map_inv, ← hV, hθσ]
      group
    refine ⟨3 - j, H * (⟨glAut σ H, glAut_mem_unitaryIsom3 σ H.2⟩ : unitaryIsom3 h)⁻¹, ?_⟩
    rw [hθ', mul_assoc, ← map_pow, ← map_mul, hone, map_one, mul_one]

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField
