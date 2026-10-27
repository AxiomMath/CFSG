module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbOneChain

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv

variable {V : Type} [CommGroup V] [Finite V]

theorem EndCfg4.oneLift_false {G T Y : Subgroup (MulAut V)} (hNL : NatLiftStatement)
    (h2 : Alt2Rank1) (h : EndCfg4 G T Y) (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ} (hm : 7 ≤ m)
    (hodd : Odd m) (hY : YAlt Y m) {t : MulAut V} (htG : t ∈ G) (htT : t ∈ T) (ht2 : t ^ 2 = 1)
    (ht1 : t ≠ 1) {X : Subgroup (MulAut V)} (hX : IsCbLift G Y t m X)
    (huniq : ∀ X' : Subgroup (MulAut V), IsCbLift G Y t m X' → X' = X) : False :=
  OneCfg.false_of_chain ⟨h, hV, hm, hodd, hY, h2, hNL, htG, htT, ht2, ht1, hX, huniq⟩

end CFSG.CGT.PushingUpLit.CGT6
