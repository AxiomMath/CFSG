module

public import CFSG.GH74.Generic.S45.LQSmall
public import CFSG.GH74.Generic.S45.LExcAssembly

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.Blueprint Subgroup CFSG.GH74.Uniqueness.Bender CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.ExcSelector
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem even_exc_false
    {S : Type} [Group S] {t : StatedLieTag} {f : ℕ} (hmodel : ChevalleyExceptionalModel S t 2 f)
    {ya : MulAut S} {Lb : Subgroup S} {q : ℕ} (hQ : QData S ya Lb q) : False := by
  have hya2 : ya ^ 2 = 1 := by rw [pow_two]; exact hQ.sq
  exact noSmallQ8Component_of_model_even hmodel ya hya2 hQ.ne Lb hQ.isComponentOf_fixed hQ.smallQ8

end CFSG.GH74.Generic.S45
