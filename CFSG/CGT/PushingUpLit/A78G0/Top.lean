module

public import CFSG.CGT.PushingUpLit.A78G0.Bridge
public import CFSG.CGT.PushingUpLit.A78G0.Dual
public import CFSG.CGT.PushingUpLit.A78G0.Sp4
public import CFSG.CGT.PushingUpLit.A78.Sp4Final
public import CFSG.CGT.PushingUpLit.C2L.Defs

public section

namespace CFSG.CGT.PushingUpLit.A78G0

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78

variable {G : Type} [Group G] [Finite G]

theorem a78SylowSp4
    {L₁ L₂ T : Subgroup G} {n : ℕ}
    (h : A78Cfg G L₁ L₂ T n) (hS : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤)
    (hZ : oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G) ≠ ⊥)
    (hJT : oTwoIn (L₁ ⊔ T) ⊔ oTwoIn (L₂ ⊔ T) = T) :
    Nonempty (G ≃* CFSG.Assembly.RankThreeEven.projSp 2 (GaloisField 2 n)) :=
  let hg := h.g0Core hS hZ hJT
  (hg.sp4Local hg.dualBase).sp4_endgame_projSp sylowOppositeSL2_holds sylowCountSL2_holds
    noSU4Abelian_holds

theorem a78SylowSp4_holds :
    C2L.A78SylowSp4 :=
  fun _ _ _ _ _ _ _ h hS hZ hJT => a78SylowSp4 h hS hZ hJT

end CFSG.CGT.PushingUpLit.A78G0
