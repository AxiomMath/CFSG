module

public import CFSG.GH74.GLS.IVK.Lifted.IIAutC
public import CFSG.GH74.GLS.IVK.Lifted.IIAutB

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GorensteinWalter
  CFSG.ABGLocalTools

section SL2

variable {F : Type} [Field F] [Finite F]

theorem mul_pgl2FieldAut_mem_range (hodd : Odd (Nat.card F)) (σ : F ≃+* F) (x : PGL2 F) :
    x * (pgl2FieldAut F σ) x ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  set R₀ := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range with hR₀
  have hOPP := isOddPrimePower_card_of_odd hodd
  have hidx : R₀.index = 2 := pgl2_psl2Range_index_eq_two F hOPP
  have hstable : ∀ τ : F ≃+* F, ∀ y ∈ R₀, (pgl2FieldAut F τ) y ∈ R₀ := by
    rintro τ _ ⟨s, rfl⟩
    exact ⟨(psl2FieldAut F τ) s, psl2FieldAut_toPGL τ s⟩
  have hsame : x⁻¹ * (pgl2FieldAut F σ) x ∈ R₀ := by
    by_cases hx : x ∈ R₀
    · exact mul_mem (R₀.inv_mem hx) (hstable σ x hx)
    · have hσx : (pgl2FieldAut F σ) x ∉ R₀ := by
        intro h
        apply hx
        have h1 : (pgl2FieldAut F σ⁻¹) ((pgl2FieldAut F σ) x) = x := by
          rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
        rw [← h1]
        exact hstable σ⁻¹ _ h
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      exact iff_of_false (fun h => hx (R₀.inv_mem_iff.1 h)) hσx
  have hxx : x * x ∈ R₀ := Subgroup.mul_self_mem_of_index_two hidx x
  have hsplit : x * (pgl2FieldAut F σ) x = (x * x) * (x⁻¹ * (pgl2FieldAut F σ) x) := by group
  rw [hsplit]
  exact mul_mem hxx hsame

theorem sl2_not_square_of_not_fixedCond (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    {Q : Type} [Group Q] (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F) (φ : MulAut Q)
    (hφ2 : φ * φ = 1) (hφout : φ ∉ innOf Q) (hnf : ¬ FixedCond Q φ) (ψ : MulAut Q) :
    ψ * ψ ≠ φ := by
  intro hψ
  set α : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) := MulAut.congr e φ with hα
  set β : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) := MulAut.congr e ψ with hβ
  have hβα : β * β = α := by rw [hα, hβ, ← map_mul, hψ]
  have hα2 : α * α = 1 := by rw [hα, ← map_mul, hφ2, map_one]
  have hr : (gammaOf hodd h3 α).right = 1 := by
    by_contra hσ
    exact hnf (fixedCond_of_congr e (fixedCond_of_field_part hodd h3 α hα2 hσ))
  have hαout : α ∉ (MulAut.conj : Matrix.SpecialLinearGroup (Fin 2) F →*
      MulAut (Matrix.SpecialLinearGroup (Fin 2) F)).range := by
    rintro ⟨s, hs⟩
    apply hφout
    refine ⟨e.symm s, ?_⟩
    apply (MulAut.congr e).injective
    rw [congr_conj, MulEquiv.apply_symm_apply, hs]
  have hleft : (gammaOf hodd h3 α).left ∉
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := fun h =>
    hαout ((mem_inn_iff hodd h3 α).2 ⟨hr, h⟩)
  have hmul : (gammaOf hodd h3 α).left = (gammaOf hodd h3 β).left *
      (pgl2FieldAut F (gammaOf hodd h3 β).right) (gammaOf hodd h3 β).left := by
    rw [← hβα, map_mul, SemidirectProduct.mul_left]
  exact hleft (hmul ▸ mul_pgl2FieldAut_mem_range hodd _ _)

end SL2

theorem a7_not_square (h2A7 : II4_2A7) {Q : Type} [Group Q] [Finite Q] (h7 : IsDoubleCoverOfAlt Q 7)
    (φ : MulAut Q) (hφout : φ ∉ innOf Q) (ψ : MulAut Q) : ψ * ψ ≠ φ := by
  intro hψ
  apply hφout
  rw [← hψ]
  exact Subgroup.mul_self_mem_of_index_two ((h2A7 Q h7).2.2.2.1) ψ

theorem pRank_eq_one_of_sl2or2a7 {Q : Type} [Group Q] [Finite Q] (hQ : IsSL2Or2A7 Q) :
    CFSG.pRank 2 Q = 1 := by
  rcases hQ.1 with ⟨F, _, _, ⟨hodd, -⟩, ⟨e⟩⟩ | h7
  · exact pRank_two_eq_one_of_sl2 hodd e
  · have hT : CFSG.GH74.Uniqueness.SU.K.IsTwoAlt Q 7 :=
      ⟨h7.1, (inferInstance : Finite Q), h7.2.1, h7.2.2⟩
    obtain ⟨π, hπ⟩ := CFSG.GH74.Uniqueness.SU.SU13.TA.TwoCover.exists_of_isTwoAlt hT
    exact pRank_eq_one_of_twoCover_seven hπ

@[expose] def SL2IsKGroup : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Odd (Nat.card F) → 3 < Nat.card F →
    IsKGroupNative (Matrix.SpecialLinearGroup (Fin 2) F)

theorem ii4_aut_d_of_kgroup (h2A7 : II4_2A7) (hK : SL2IsKGroup) : II4_Aut_d := by
  intro Q _ _ hQ φ hφ2 hφout hnf ψ
  rcases sl_or_a7 hQ with ⟨F, _, _, hodd, h3, ⟨e⟩⟩ | h7
  · have hKQ : IsKGroupNative Q := SectionRank.IsKGroupCat.of_mulEquiv (hK F hodd h3) e
    have hnfc : ¬ FixedCond Q φ := fun hf =>
      hnf (isFAutomorphism_of_fixedCond (isQuasisimple_of_sl2or2a7 hQ) hKQ
        (pRank_eq_one_of_sl2or2a7 hQ) hφ2 hf)
    exact sl2_not_square_of_not_fixedCond hodd h3 e φ hφ2 hφout hnfc ψ
  · exact a7_not_square h2A7 h7 φ hφout ψ

theorem ii4_aut_of_kgroup
    (h2A7 : II4_2A7) (hK : SL2IsKGroup) : II4_Aut :=
  ii4_aut_of_parts (ii4_aut_a h2A7) ii4_aut_b ii4_aut_c (ii4_aut_d_of_kgroup h2A7 hK)

end CFSG.GH74.GLS.IVK.Lifted
