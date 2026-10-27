module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRONan
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSporXONFix
public import CFSG.Sporadic.ONOddCore.FixedRankOne

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR

open CFSG Subgroup CFSG.Blueprint CFSG.ONSchreier
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem on_outer_not_isPGroup
    {α : MulAut Pv} (hout : α ∉ (MulAut.conj : Pv →* MulAut Pv).range) (hα2 : α * α = 1) :
    ¬ IsPGroup 2 ↥(fixedSubgroup α) := by
  obtain ⟨⟨V, hVα, hVab, hV4⟩, -⟩ :=
    CFSG.Sporadic.ONOddCore.glq_sporadic_outer_involution_fixed_rank_one_ON_exclusion
      ⟨onEquivPv.symm⟩ α hα2
  obtain ⟨a, haV, ha1⟩ : ∃ a ∈ V, a ≠ 1 := by
    by_contra hcon
    have hbot : V = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      by_contra hx1
      exact hcon ⟨x, hx, hx1⟩
    rw [hbot, Subgroup.card_bot] at hV4
    exact absurd hV4 (by norm_num)
  have ha2 : orderOf a = 2 :=
    orderOf_eq_prime (CFSG.elemPow_eq_one_of_isElementaryAbelian (A := V) a haV) ha1
  obtain ⟨x, hx, -, hxo⟩ := Hin.SporX.exists_fixed_odd_of_fix hout hα2 ha2 (hVα haV)
  have hodd : Odd (orderOf x) := by
    rcases hxo with h | h <;> rw [h] <;> decide
  refine not_isPGroup_of_pow (g := (⟨x, hx⟩ : ↥(fixedSubgroup α))) hodd ?_ ?_
  · apply Subtype.ext
    change x ^ orderOf x = 1
    exact pow_orderOf_eq_one x
  · intro h
    have h1 : x = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hxo
    rcases hxo with h | h <;> exact absurd h (by decide)

theorem onOuterNoTwoFix_holds
    : ONOuterNoTwoFix := fun _ hout hα2 => on_outer_not_isPGroup hout hα2

theorem sporNoTwoFix_ONan
    : SporNoTwoFix .ONan :=
  sporNoTwoFix_ONan_of_outer onOuterNoTwoFix_holds

end CFSG.ComponentClassification.HarrisLit.L33.SR
