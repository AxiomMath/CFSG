module

public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L510

open Matrix CFSG CFSG.GorensteinWalter CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Lifted
  CFSG.GH74.GLS.Stage1.Thm2.Recip

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem psl2AutHom_slFieldAut (σ : F ≃+* F) : psl2AutHom (slFieldAut σ) = psl2FieldAut F σ := by
  ext x
  induction x using QuotientGroup.induction_on with | H b => ?_
  change psl2AutHom (slFieldAut σ) (QuotientGroup.mk' _ b) =
    psl2FieldAut F σ (QuotientGroup.mk' _ b)
  rw [psl2FieldAut_apply, psl2RingEquiv_mk]
  exact CFSG.ABGLocalTools.psl2MulAutOf_mk (slFieldAut σ) b

theorem psl2AutHom_surjective (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) :
    Function.Surjective (psl2AutHom (F := F)) := by
  intro ψ
  set γ : PGammaL2 F := (thetaEquiv hodd h3).symm ψ with hγ
  obtain ⟨G, hG⟩ := Matrix.ProjGenLinGroup.mk_surjective γ.left
  refine ⟨CFSG.Semidihedral.MatrixCoverData.slConjugation F G * slFieldAut γ.right, ?_⟩
  rw [map_mul, psl2AutHom_slFieldAut]
  rw [show psl2AutHom (CFSG.Semidihedral.MatrixCoverData.slConjugation F G) =
      thetaEquiv hodd h3 (SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk G)) from
    psl2MulAutOf_slConjugation hodd h3 G]
  rw [hG, ← thetaEquiv_inr hodd h3, ← map_mul, SemidirectProduct.inl_left_mul_inr_right, hγ,
    MulEquiv.apply_symm_apply]

theorem fixedCond_slFieldAut_all (hodd : Odd (Nat.card F)) (σ : F ≃+* F) :
    FixedCond (SpecialLinearGroup (Fin 2) F) (slFieldAut σ) := by
  have hq₀odd : Odd (Nat.card ↥(fixedField σ)) := odd_card_fixedField σ hodd
  have hq₀gt : 1 < Nat.card ↥(fixedField σ) := one_lt_card_fixedField σ
  apply fixedCond_of_equiv (slFieldAut σ) (fixedEquivSL σ)
  by_cases h3 : Nat.card ↥(fixedField σ) = 3
  · right
    have hO := pPrimeCore_two_sl2_three (K := fixedField σ) h3
    refine ⟨⊤, Subgroup.IsSubnormal.top, ↥(fixedField σ), inferInstance, inferInstance, h3, ⟨?_⟩⟩
    exact Subgroup.topEquiv.trans
      (((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 ↥(fixedField σ)))
  · left
    have h5 : 5 ≤ Nat.card ↥(fixedField σ) := by
      obtain ⟨k, hk⟩ := hq₀odd
      omega
    exact ⟨⊤, isPComponent_top (isQuasisimple_sl2' (by omega))
      (pPrimeCore_two_sl2_five hq₀odd h5)⟩

theorem fixedCond_of_twisted_field (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (α : MulAut (SpecialLinearGroup (Fin 2) F)) (ψ : MulAut (PSL2 F)) (σ : F ≃+* F)
    (h : psl2AutHom α = ψ⁻¹ * psl2FieldAut F σ * ψ) :
    FixedCond (SpecialLinearGroup (Fin 2) F) α := by
  obtain ⟨β, hβ⟩ := psl2AutHom_surjective hodd h3 ψ
  have e1 : MulAut.congr β⁻¹ (slFieldAut σ) = β⁻¹ * slFieldAut σ * β := by
    ext x
    simp [MulAut.congr_apply, MulAut.mul_apply]
  have hαeq : α = MulAut.congr β⁻¹ (slFieldAut σ) := by
    apply psl2AutHom_injective hodd h3
    rw [e1, map_mul, map_mul, map_inv, psl2AutHom_slFieldAut, hβ, h]
  rw [hαeq]
  exact fixedCond_congr β⁻¹ (fixedCond_slFieldAut_all hodd σ)

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L510
