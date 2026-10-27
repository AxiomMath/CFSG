module

public import CFSG.CharacterTheory.TwoRankLowerBound.AbelianRankOne
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionAffineOddPair

variable {Y K : Type*} [Group Y] [Group K]

theorem no_four_group_of_injective
    (hno : ∀ V : Subgroup Y, ¬ IsKleinFour V)
    (f : K →* Y) (hf : Function.Injective f) :
    ∀ V : Subgroup K, ¬ IsKleinFour V := by
  intro V hV
  let := hV
  let e := V.equivMapOfInjective f hf
  apply hno (V.map f)
  constructor
  · exact (Nat.card_congr e.toEquiv).symm.trans IsKleinFour.card_four
  · exact (Monoid.exponent_eq_of_mulEquiv e).symm.trans IsKleinFour.exponent_two

theorem commuting_involutions_eq_of_no_four_group [Finite Y]
    (hno : ∀ V : Subgroup Y, ¬ IsKleinFour V)
    (x y : Y) (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hc : Commute x y) : x = y := by
  by_contra hne
  let V := CFSG.TwoRankLowerBound.Helpers.involutionPairSubgroup x y
    (hx ▸ pow_orderOf_eq_one x) (hy ▸ pow_orderOf_eq_one y) hc
  have hVcard : Nat.card V = 4 :=
    CFSG.TwoRankLowerBound.Helpers.involutionPairSubgroup_card x y hx hy hne hc
  have hVelem := CFSG.TwoRankLowerBound.Helpers.involutionPairSubgroup_elementary x y
    (hx ▸ pow_orderOf_eq_one x) (hy ▸ pow_orderOf_eq_one y) hc
  let : IsElementaryAbelian 2 V :=
    { toIsMulCommutative := hVelem.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        (fun v => Subtype.ext (hVelem.2 v v.property)) }
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  exact hno V ⟨hVcard, IsElementaryAbelian.exponent_eq_prime⟩

theorem no_four_group_two_rank_le_one [Finite Y]
    (hno : ∀ V : Subgroup Y, ¬ IsKleinFour V) (hp : IsPGroup 2 Y) :
    CFSG.Open.twoRank Y ≤ 1 := by
  apply CFSG.TwoRankLowerBound.Helpers.twoRank_le_one_of_abelian_subgroups_cyclic Y
  intro B hBcomm
  let := hBcomm
  let : CommGroup B := Group.commGroupOfCenterEqTop Subgroup.center_eq_top
  have hBp := hp.to_subgroup B
  obtain ⟨n, hn⟩ := hBp.exists_card_eq
  apply CFSG.TwoRankLowerBound.Helpers.abelian_two_group_cyclic_of_unique_involution_of_card_eq_pow
    n B hBp hn
  intro x y hx hy
  apply Subtype.ext
  exact commuting_involutions_eq_of_no_four_group hno x y
    ((Subgroup.orderOf_coe x).trans hx) ((Subgroup.orderOf_coe y).trans hy)
    (congrArg Subtype.val (mul_comm x y))

end CFSG.ProperTwoGeneratedCore.LocalCriterionAffineOddPair
