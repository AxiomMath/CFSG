module

public import CFSG.GH74.GLS.Stage1.Main.Closed
public import CFSG.GH74.GLS.TwoThin.G.Section
public import CFSG.GH74.GLS.IVK.Lifted.TwoCoverRank
public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticOddSections

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Blueprint Assembly.LowTwoRank CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Main
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.Uniqueness.SU.SU13.TA

theorem statedSL_two_involution_unique {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    {t₁ t₂ : StatedSL 2 F} (h₁ : orderOf t₁ = 2) (h₂ : orderOf t₂ = 2) : t₁ = t₂ := by
  have h2 : (2 : F) ≠ 0 := by
    intro h
    apply CFSG.GH74.GLS.neg_one_ne_one_of_odd_card F hodd
    have h11 : (1 : F) + 1 = 0 := by
      rw [one_add_one_eq_two]
      exact h
    exact neg_eq_of_add_eq_zero_right h11
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F
  have key : ∀ t : StatedSL 2 F, orderOf t = 2 →
      ((e.symm t : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = -1 := by
    intro t ht
    have hord : orderOf (e.symm t) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact ht
    refine CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 _ ?_ ?_
    · have := pow_orderOf_eq_one (e.symm t)
      rwa [hord] at this
    · intro h1
      rw [h1, orderOf_one] at hord
      exact absurd hord (by norm_num)
  have : e.symm t₁ = e.symm t₂ :=
    Matrix.SpecialLinearGroup.ext _ _ fun i j => by rw [key t₁ h₁, key t₂ h₂]
  exact e.symm.injective this

theorem pRank_two_eq_one_of_sl2 {X F : Type} [Group X] [Finite X] [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (e : X ≃* StatedSL 2 F) : CFSG.pRank 2 X = 1 := by
  obtain ⟨z₀, -, hz₀⟩ := TwoThin.exists_central_involution_statedSL_two F hodd
  refine pRank_two_eq_one_of_unique_involution (u := e.symm z₀) ?_ ?_
  · rw [MulEquiv.orderOf_eq]
    exact hz₀
  · intro t ht
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    exact statedSL_two_involution_unique hodd (by rw [MulEquiv.orderOf_eq]; exact ht) hz₀

theorem b2_split
    : B2Split := by
  intro G _ _ K hB hne
  have hrank : CFSG.pRank 2 (HatT K) = CFSG.pRank 2 ↥K := pRank_two_quot_pPrimeCore ↥K
  rcases TwoThin.inB2_cases hB with ⟨F, _, _, hodd, ⟨e⟩⟩ | ⟨n, h7, h11, hcov⟩ | ⟨hL34, hexp⟩
  · exact absurd (hrank.symm.trans (pRank_two_eq_one_of_sl2 hodd e)) hne
  · have hT : CFSG.GH74.Uniqueness.SU.K.IsTwoAlt (HatT K) n :=
      ⟨hcov.1, (inferInstance : Finite (HatT K)), hcov.2.1, hcov.2.2⟩
    obtain ⟨π, hπ⟩ := TwoCover.exists_of_isTwoAlt hT
    by_cases hn : n = 7
    · subst hn
      exact absurd (hrank.symm.trans (pRank_eq_one_of_twoCover_seven hπ)) hne
    · left
      refine ⟨n, by omega, h11, hcov, ?_⟩
      rw [← hrank]
      exact four_le_pRank_of_twoCover hπ (by omega)
  · exact Or.inr ⟨hB.1.1, hL34, hexp⟩

end CFSG.GH74.GLS.IVK.Lifted
