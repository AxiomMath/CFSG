module

public import CFSG.GH74.QTGen4.Recog.G23.MSylowC
public import CFSG.GH74.QTGen4.Recog.G23.MSylowD

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G23Type
open scoped MatrixGroups

variable {G : Type*} [Group G]

theorem G23Two.card_involutions_sylow_of_hR [Finite G] {M T : Subgroup G} (hM : G23Two M)
    (hTM : T ≤ M) (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ (T.subgroupOf M).index)
    (hR : ∃ x ∈ M, x * x = 1 ∧ x ∉ quasithinGenFitting M) :
    Nat.card {t : ↥T // orderOf t = 2} = 27 :=
  G23Two.card_involutions_sylow_of_outside hM hTM hT2 hTidx hR SL3_two_involutions_conj
    SL3_two_order_eight_involutions

end CFSG.GH74.QTGen4.Recog.G23
