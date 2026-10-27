module

public import CFSG.ClassicalInvolution.Q3.TL4Thm6Below
public import CFSG.ClassicalInvolution.Q3.TL4StepDefs
public import CFSG.ClassicalInvolution.Q3.TA3SmallBase
public import CFSG.ClassicalInvolution.Q3.TL3F1Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic


theorem smallSimple6_of_leaves (hGH : GH74SectionalModels) (hL : SmallLeaves6) (Y : Type)
    [Group Y] [Finite Y] [IsSimpleGroup ↥(genFittingFStar Y)] (hA : CIT3Below (Nat.card Y))
    (hnab : ∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a)
    (hP : TwoSubgroupsFourGenerated ↥(genFittingFStar Y)) (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (hd : TightDatum R S t) (hc : TightCls Y R S t) (hE2 : ¬ TightInO2 t) :
    GoodThreeElement R t ∨ Thm6Exit Y := by
  rcases TA3.smallList hGH _ hnab hP with
    (h | h | h | h | h | h | h | h | h | h | h | h | h) | hex
  · exact hL.g2 Y hA hnab hP h R S t hd hc hE2
  · exact hL.d4 Y hA hnab hP h R S t hd hc hE2
  · exact hL.psp4 Y hA hnab hP h R S t hd hc hE2
  · exact hL.twistedG2 Y hA hnab hP h R S t hd hc hE2
  · exact hL.l4 Y hA hnab hP h R S t hd hc hE2
  · exact hL.u4 Y hA hnab hP h R S t hd hc hE2
  · exact hL.l5 Y hA hnab hP h R S t hd hc hE2
  · exact hL.u5 Y hA hnab hP h R S t hd hc hE2
  · exact hL.m12 Y hA hnab hP h R S t hd hc hE2
  · exact hL.l2 Y hA hnab hP h R S t hd hc hE2
  · exact hL.l3 Y hA hnab hP h R S t hd hc hE2
  · exact hL.u3 Y hA hnab hP h R S t hd hc hE2
  · exact hL.m11 Y hA hnab hP h R S t hd hc hE2
  · exfalso
    have := genFittingFStar_normal Y
    obtain ⟨r, hr, ⟨eS⟩⟩ := hd.quat
    exact (Nobq.smallNoDatum_of_dvd Nobq.card_outer_Ly_dvd_two).noDatum _ hex Y
      (genFittingFStar Y) ⟨MulEquiv.refl _⟩ (Nobq.centralizer_genFittingFStar_eq_bot hnab) R S r
      hr ⟨eS⟩ t hd.mem hd.order hd.cent hd.normal

theorem thm6SimpleLe_of_leaves (hGH : GH74SectionalModels) (hL : SmallLeaves6) {n : ℕ}
    (hA : CIT3Below n) (hb : TightBelow n) : Thm6SimpleLe n := by
  intro Y _ _ _ hY hnab R S t hd hc hE2 he
  have hA' : CIT3Below (Nat.card Y) := fun Y' _ _ hY' Λ hΛ => hA Y' (lt_of_lt_of_le hY' hY) Λ hΛ
  by_cases hsmall : TwoSubgroupsFourGenerated ↥(genFittingFStar Y)
  · exact smallSimple6_of_leaves hGH hL Y hA' hnab hsmall R S t hd hc hE2
  · exact absurd he (tightLargeEdgeS_holds (Nat.card Y) hA'
      (tightBelowR_three_iff.mp (Induct.tightBelowR_mono hY (tightBelowR_three_iff.mpr hb)))
      Y rfl hnab R S t hd hc hE2 hsmall)

theorem thm6StepR_three_of_leaves (hGH : GH74SectionalModels) (hL : SmallLeaves6) (n : ℕ) :
    Thm6StepR 3 n :=
  fun hA hP => thm6RBelow_three_of_simple (thm6SimpleLe_of_leaves hGH hL hA (tightBelow_of_plus hP))

end CFSG.ClassicalInvolution.Q3.TL4
