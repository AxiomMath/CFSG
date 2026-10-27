module

public import CFSG.CGT.PushingUpLit.A78.Sp4Endgame
public import CFSG.CGT.PushingUpLit.A78.OppSL2
public import CFSG.CGT.PushingUpLit.A78.NoSU4

public section

namespace CFSG.CGT.PushingUpLit.A78

theorem sylowOppositeSL2_holds : SylowOppositeSL2 :=
  fun he φ hA hB hAc hBc hAB => opposite_of_sylow_sl2 he φ hA hB hAc hBc hAB

theorem sylowCountSL2_holds : SylowCountSL2 :=
  fun he φ => ncard_sylow_sl2 he φ

theorem noSU4Abelian_holds : NoSU4Abelian :=
  fun hf Φ hs hk => su4_exists_big_abelian hf Φ hs hk

variable {G : Type} [Group G] [Finite G] {Z : Subgroup G} {e : ℕ}

end CFSG.CGT.PushingUpLit.A78
