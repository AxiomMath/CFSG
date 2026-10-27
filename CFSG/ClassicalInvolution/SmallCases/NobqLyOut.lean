module

public import CFSG.ClassicalInvolution.SmallCases.NobqFinalDvd

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.ComponentClassification.OuterAutomorphisms

theorem card_outer_Ly_dvd_two : Nat.card (Outer NativeSporadic.Ly) ∣ 2 := by
  have h := CFSG.Sporadic.LySchreier.outer_order_divides_two (T := NativeSporadic.Ly)
    ⟨MulEquiv.refl _⟩
  exact h.1

theorem normalOddByQuaternionSmall_of_gh74' (hGH : GH74SectionalModels) :
    NormalOddByQuaternionUnder fun {G} _ _ _ => TwoSubgroupsFourGenerated (genFittingFStar G) :=
  normalOddByQuaternionSmall_of_outLy_dvd hGH card_outer_Ly_dvd_two

end CFSG.ClassicalInvolution.Nobq
