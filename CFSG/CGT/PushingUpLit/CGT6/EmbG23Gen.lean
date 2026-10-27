module

public import CFSG.CGT.PushingUpLit.CGT6.EmbG23Cfg
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.K7bX

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Blueprint CFSG.LieType.Ree

section Main


theorem end412_generation {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}
    (h : EndCfg4 G T Y) (hY : YSL Y 3) (hout : OuterT G T Y)
    (hm : ChevalleyExceptionalModel (LayerQ G Y) .G2 3 1)
    (S : Subgroup (MulAut V)) (hSY : S ≤ Y) (hS8 : Nat.card S = 8) :
    ∃ g ∈ conjClosure Y G, g ∈ Subgroup.normalizer (S : Set (MulAut V)) ∧
      Y ⊔ Y.map (MulAut.conj g).toMonoidHom = conjClosure Y G := by
  have : CharP (ZMod 3) ReeTag.G2.prime := ZMod.charP 3
  exact end412_generation_of_pinned EmbModule.g23_pinned h hY hout hm S hSY hS8

end Main

end CFSG.CGT.PushingUpLit.CGT6
