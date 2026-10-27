module

public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.ABGLocalTools
  CFSG.ABGDGroups CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

section Sign

variable {F : Type} [Field F] [Finite F]

open CFSG.Semidihedral.SemilinearOuterQuotient (SquareClass)

theorem sign_aut (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (α : MulAut (SpecialLinearGroup (Fin 2) F)) (k : SpecialLinearGroup (Fin 2) F)
    (hk : α ^ orderOf (gammaOf hodd h3 α).right = MulAut.conj k) (hαk : α k = k) :
    pGammaL2DetClass F (isOddPrimePower_card_of_odd hodd) (gammaOf hodd h3 α) = 1 := by
  have hK := isOddPrimePower_card_of_odd hodd
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  by_contra hne
  set x := gammaOf hodd h3 α with hx
  obtain ⟨G, hG⟩ := Matrix.ProjGenLinGroup.mk_surjective x.left
  have hθ : pGammaL2ToMulAutPSL2 F hK h3 x = psl2MulAutOf α := thetaEquiv_gammaOf hodd h3 α
  have hα := semilinear_of_pGammaL2 hodd h3 α x hθ G hG
  have hsq := sign_lemma_matrix h2 α G x.right hα k hk hαk
  apply hne
  rw [← left_mem_range_toPGL_iff hK, ← hG, pgl2_mk_mem_psl2_range_iff_det_isSquare,
    Matrix.GeneralLinearGroup.val_det_apply]
  exact hsq

theorem pow_mem_inn_of_even (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (α : MulAut (SpecialLinearGroup (Fin 2) F))
    (hev : Even (orderOf (gammaOf hodd h3 α).right)) :
    α ^ orderOf (gammaOf hodd h3 α).right ∈
      (MulAut.conj : SpecialLinearGroup (Fin 2) F →* MulAut (SpecialLinearGroup (Fin 2) F)).range := by
  have hK := isOddPrimePower_card_of_odd hodd
  rw [mem_inn_iff hodd h3, map_pow]
  constructor
  · show SemidirectProduct.rightHom (gammaOf hodd h3 α ^ orderOf (gammaOf hodd h3 α).right) = 1
    rw [map_pow]
    exact pow_orderOf_eq_one _
  · rw [left_mem_range_toPGL_iff hK, map_pow]
    obtain ⟨m, hm⟩ := hev
    rw [hm, ← two_mul, pow_mul]
    have := squareClass_sq (pGammaL2DetClass F hK (gammaOf hodd h3 α))
    rw [this, one_pow]

end Sign

section Cyclic

variable {F : Type} [Field F] [Finite F] {Q : Type} [Group Q]

open CFSG.Semidihedral.SemilinearOuterQuotient (SquareClass)

theorem isCyclic_of_signs (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (e : Q ≃* SpecialLinearGroup (Fin 2) F) {X : Type} [Group X] (φ : X →* MulAut Q)
    (N : Subgroup X) [N.Normal] (hN : ∀ x, x ∈ N ↔ φ x ∈ innOf Q)
    (hlift : ∀ x : X, Even (orderOf (gammaOf hodd h3 (MulAut.congr e (φ x))).right) →
      ∃ k : Q, φ x ^ orderOf (gammaOf hodd h3 (MulAut.congr e (φ x))).right = MulAut.conj k ∧
        φ x k = k) :
    IsCyclic (X ⧸ N) := by
  have hK := isOddPrimePower_card_of_odd hodd
  have : IsCyclic (F ≃+* F) := isCyclic_ringEquiv F
  let γ : X →* PGammaL2 F := (gammaOf hodd h3).comp ((MulAut.congr e).toMonoidHom.comp φ)
  let Ψ : X →* SquareClass F × (F ≃+* F) :=
    ((pGammaL2DetClass F hK).comp γ).prod (SemidirectProduct.rightHom.comp γ)
  have hker : Ψ.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, hN]
    have hin : φ x ∈ innOf Q ↔ MulAut.congr e (φ x) ∈
        (MulAut.conj : SpecialLinearGroup (Fin 2) F →* MulAut (SpecialLinearGroup (Fin 2) F)).range := by
      constructor
      · rintro ⟨c, hc⟩
        exact ⟨e c, by rw [← congr_conj e c, hc]⟩
      · rintro ⟨s, hs⟩
        refine ⟨e.symm s, ?_⟩
        apply (MulAut.congr e).injective
        rw [congr_conj, MulEquiv.apply_symm_apply, hs]
    rw [hin, mem_inn_iff hodd h3, left_mem_range_toPGL_iff hK]
    show (pGammaL2DetClass F hK (γ x), SemidirectProduct.rightHom (γ x)) = 1 ↔ _
    rw [Prod.mk_eq_one]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1⟩
  have e1 : X ⧸ N ≃* Ψ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange Ψ)
  rw [e1.isCyclic]
  refine isCyclic_of_sign (CFSG.Semidihedral.SemilinearOuterQuotient.squareClass_card_two F hK) _ ?_
  rintro _ ⟨x, rfl⟩ hev
  have hev' : Even (orderOf (gammaOf hodd h3 (MulAut.congr e (φ x))).right) := hev
  obtain ⟨k, hk, hkfix⟩ := hlift x hev'
  refine sign_aut hodd h3 (MulAut.congr e (φ x)) (e k) ?_ ?_
  · rw [← map_pow, hk, congr_conj]
  · show (MulAut.congr e (φ x)) (e k) = e k
    rw [MulAut.congr_apply]
    simp [hkfix]

end Cyclic

section ClaimB

variable {F : Type} [Field F] [Finite F] {Q : Type} [Group Q]

theorem not_fixedCond_of_right_eq_one (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (e : Q ≃* SpecialLinearGroup (Fin 2) F) (φ : MulAut Q) (hφ1 : φ ≠ 1)
    (hσ : (gammaOf hodd h3 (MulAut.congr e φ)).right = 1) : ¬ FixedCond Q φ := by
  intro hf
  have hα1 : MulAut.congr e φ ≠ 1 := fun h =>
    hφ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  obtain ⟨G, hG⟩ := eq_slConjugation_of_right_eq_one hodd h3 _ hσ
  apply not_fixedCond_of_comm φ _ hf
  apply comm_fixed_of_congr e φ
  rw [hG]
  exact fixed_comm_of_slConjugation G (hG ▸ hα1)

end ClaimB

end CFSG.GH74.GLS.IVK.Lifted
