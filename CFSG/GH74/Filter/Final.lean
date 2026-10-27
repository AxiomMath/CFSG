module

public import CFSG.GH74.Filter.Small.Wrappers
public import CFSG.GH74.Filter.Small.Unipotent
public import CFSG.GH74.Filter.Small.Exceptional
public import CFSG.GH74.Filter.Small.Alternating
public import CFSG.GH74.Filter.Small.RankThree
public import CFSG.GH74.Filter.ClassicalOdd.Symplectic
public import CFSG.GH74.Filter.Orthogonal.EvenEichler
public import CFSG.GH74.Filter.Orthogonal.OddReflections
public import CFSG.GH74.Filter.Orthogonal.SymplecticSix
public import CFSG.GH74.Filter.Orthogonal.UnitaryEven
public import CFSG.GH74.Filter.Lie.EvenSeries
public import CFSG.GH74.Filter.Lie.Suzuki
public import CFSG.GH74.Filter.Lie.TwistedF4
public import CFSG.GH74.Filter.Lie.TitsElem
public import CFSG.GH74.Filter.Lie.TwistedE6Even
public import CFSG.GH74.Filter.Lie.TwistedD4Even
public import CFSG.GH74.Filter.Lie.TwistedE6Odd
public import CFSG.GH74.Filter.Sporadic.All
public import CFSG.GH74.Filter.Monster.Main

public section

namespace CFSG.GH74.Filter

open Blueprint

theorem filter
    : ∀ (G : Type) [Group G] [Finite G], Catalog G → (∃ a b : G, a * b ≠ b * a) →
    3 ≤ Open.twoRank G → Gen4 G → GH74Conclusion G :=
  filter_of_families
    t_alt_small t_alt_large t_iso_L4_two t_iso_U4_two
    t_PSL_two_odd t_PSL_three_odd t_PSL_two_four t_PSL_three_two t_PSL_even_unipotent
    t_PSL_four_odd t_PSL_five_odd t_PSL_six_odd t_PSL_ge_seven_odd
    t_PSU_three_odd t_PSU_three_four t_PSU_even t_PSU_four_odd
    t_PSU_five_odd t_PSU_six_odd t_PSU_ge_seven_odd
    t_PSp_even_unipotent t_PSp_three_two t_PSp_odd_ge_three
    t_POmegaOdd t_POmegaPlus_odd t_POmegaMinus_odd t_POmegaPlus_even t_POmegaMinus_even
    t_G2_even t_F4_even t_E6_even t_E7_even t_E8_even t_2E6_even t_3D4_even
    t_F4_odd t_E6_odd t_E7_odd t_E8_odd t_2E6_odd
    t_suzuki_large t_twistedF4 t_Tits t_M11
    (t_sporadic_all t_sporadic_M)

end CFSG.GH74.Filter
