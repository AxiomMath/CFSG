module

public import CFSG.CGT.PushingUpLit.CGT6.EmbMin

public section

namespace CFSG.CGT.PushingUpLit.CGT6

variable {V : Type} [CommGroup V] [Finite V]

theorem Smaller.of_lt {H G : Subgroup (MulAut V)} (h : H < G) : Smaller H G :=
  Or.inl (lt_of_not_ge fun hge => h.ne (Subgroup.eq_of_le_of_card_ge h.le hge))

theorem Emb5Cfg.lift_sub {G T Y : Subgroup (MulAut V)} (cfg : Emb5Cfg G T Y)
    (hV : ∀ v : V, v ^ 2 = 1) {H : Subgroup (MulAut V)} (hHG : H < G)
    {T' Y' : Subgroup (MulAut V)} (hadm : Adm5 H T' Y') : ∃ X, Lift5 H Y' X :=
  cfg.ih V hV H (Smaller.of_lt hHG) (isKGroup_of_le cfg.kgroup hHG.le) T' Y' hadm

end CFSG.CGT.PushingUpLit.CGT6
