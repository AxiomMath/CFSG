module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporRows

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.I271.I1415ALy

open CFSG.HardMathSupport.Dickson.I271
open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.Yardstones.Md0ec50421ce4
  CFSG.Sporadic.Recognition.LyonsSims CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open CFSG.LocalAnalysis.GLTheoremA.I1416Rows CFSG.LocalAnalysis.GLTheoremA.I1415Rows
open Subgroup Equiv

theorem atypeOK_McL (hb : LieOrderBridge) : ATypeOK 3 NativeSporadic.McL := by
  have hc : Nat.card NativeSporadic.McL = 898128000 := CFSG.Sporadic.McL.card_McL
  haveI : Finite NativeSporadic.McL := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact atypeOK_of_card hb (N := 898128000) (by rw [hc] <;> norm_num) (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide)

section Main


theorem arow_Ly_three (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges) (hb : LieOrderBridge) :
    I1415Row .Ly 3 := by
  have hc : Nat.card (NativeSporadic.Carrier .Ly) = 51765179004000000 :=
    CFSG.Sporadic.Ly.card_Ly
  haveI : Finite (NativeSporadic.Carrier .Ly) := CFSG.Sporadic.Ly.fam_ly_simplicity.1
  haveI : IsSimpleGroup (NativeSporadic.Carrier .Ly) := CFSG.Sporadic.Ly.fam_ly_simplicity.2.2
  have hS : Nonempty (NativeSporadic.Carrier .Ly ≃* NativeSporadic.Carrier .Ly) :=
    ⟨MulEquiv.refl _⟩
  obtain ⟨t, ρ, D⟩ :=
    exists_lyData_of_oneClassDoubleCover (LyMult.oneClassDoubleCover_of_ly hS)
  obtain ⟨x₁, x₂, x₃, St⟩ := D.exists_lyStd
  have hA : ACompOK 3 (x₁ : NativeSporadic.Carrier .Ly) := by
    obtain ⟨eP⟩ := tabLy_pSimple D St
    refine acompOK_of_shapeRkAt Nat.prime_three
      (Good := fun T _ => Nonempty (T ≃* NativeSporadic.McL)) (Rk := fun _ _ => True)
      (shapeRkAt_of_normal_quasisimple Nat.prime_three le_rfl
        (fun g hg l hl => Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hl) (Subgroup.inv_mem _ hg))
        (tabLy_quasisimple D St) (tabLy_three_dvd St) (tabLy_isPGroup_cent D St) ⟨eP⟩ trivial)
      ?_
    rintro T _ ⟨f⟩
    exact @ATypeOK.of_mulEquiv 3 NativeSporadic.McL T _ _ f.symm (atypeOK_McL hb)
  have hB : ACompOK 3 ((x₁ : NativeSporadic.Carrier .Ly) * (x₂ : NativeSporadic.Carrier .Ly)) :=
    acompOK_of_pConstrained Nat.prime_three
      (tabLy_threeB D St (LyCore.lyThreeBOrder_thm _ hS t ρ D x₁ x₂ x₃ St)
        (oPrimeCoreTrivialAt_Ly_three _ hS _ (tabLy_orderOf_x₁x₂ D St)))
  have htr : ∀ {a b : NativeSporadic.Carrier .Ly}, IsConj a b → ACompOK 3 a → ACompOK 3 b := by
    intro a b hab ha
    obtain ⟨c, hc⟩ := isConj_iff.1 hab
    have := ACompOK.of_mulEquiv Nat.prime_three (MulAut.conj c) ha
    rwa [MulAut.conj_apply, hc] at this
  refine arow_of_model hOut (hbr .Ly).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    fun k hk => ?_
  rcases (lemma45_classes_of_certificate D St).1 k hk with h | h
  · exact htr h.symm hA
  · exact htr h.symm hB

end Main

end CFSG.HardMathSupport.Dickson.I271.I1415ALy
