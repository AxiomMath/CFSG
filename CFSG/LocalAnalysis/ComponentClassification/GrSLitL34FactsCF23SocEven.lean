module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23SocBase
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdEven
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.ComponentClassification.GSThmB.Soc

open CFSG Subgroup CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {N : Subgroup G} [N.Normal] {α : G} {J : Subgroup G}

namespace Hyp

theorem false_of_not_seven_dvd (h : Hyp N α J)
    (hN : ¬ 7 ∣ Nat.card N) : False :=
  hN h.seven_dvd_card_N

theorem false_of_psl_two_sixteen (h : Hyp N α J)
    (hm : Blueprint.LieModel N .PSL 2 2 4) : False := by
  apply h.false_of_not_seven_dvd
  rw [(Timmesfeld.card_statedClassicalModel_two
    (RestrictedStd.statedClassicalModel_of_lieModel_PSL hm)).1 rfl]
  decide

theorem false_of_psu_three_four (h : Hyp N α J)
    (hm : Blueprint.LieModel N .PSU 3 2 2) : False := by
  apply h.false_of_not_seven_dvd
  rw [(Timmesfeld.card_statedClassicalModel_two
    (RestrictedStd.statedClassicalModel_of_lieModel (by decide) hm)).2.1 rfl]
  decide

theorem false_of_psp_four_four (h : Hyp N α J)
    (hm : Blueprint.LieModel N .PSp 2 2 2) : False := by
  apply h.false_of_not_seven_dvd
  rw [(Timmesfeld.card_statedClassicalModel_two
    (RestrictedStd.statedClassicalModel_of_lieModel (by decide) hm)).2.2.1 rfl]
  decide

theorem false_of_psu_five_two (h : Hyp N α J)
    (hm : Blueprint.LieModel N .PSU 5 2 1) : False := by
  apply h.false_of_not_seven_dvd
  rw [(Timmesfeld.card_statedClassicalModel_two
    (RestrictedStd.statedClassicalModel_of_lieModel (by decide) hm)).2.1 rfl]
  decide

theorem false_of_psl_three_four [Finite G] (h : Hyp N α J)
    (hm : Blueprint.LieModel N .PSL 3 2 2) : False := by
  have hN : Nat.card N = 20160 := by
    rw [(Timmesfeld.card_statedClassicalModel_two
      (RestrictedStd.statedClassicalModel_of_lieModel_PSL hm)).1 rfl]
    decide
  have hJpos : 0 < Nat.card J := Nat.card_pos
  have hJN : J = N := by
    refine Subgroup.eq_of_le_of_card_ge h.le_N ?_
    rw [hN]
    exact Nat.le_of_dvd hJpos h.dvd_card_J
  apply h.ne_top
  rw [hJN, subgroupOf_self]

end Hyp

end CFSG.ComponentClassification.GSThmB.Soc
