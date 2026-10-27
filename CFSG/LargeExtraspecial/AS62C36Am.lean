module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Geom
public import CFSG.Quasithin.Background.F1Amalgam

public section

namespace CFSG.LargeExtraspecial

open CFSG.Quasithin CFSG.Quasithin.H13.F431

namespace AS62

variable {G : Type} [Group G] {H : Subgroup G}

@[expose] def amPhi1 {M₀ : Subgroup G}
    (φ : (RankTwoAmalgam.ofSubgroups M₀ H).Iso (RankTwoAmalgam.ofSubgroups U42.P1 U42.P2)) :
    ↥M₀ ≃* ↥U42.P1 :=
  φ.φ1

@[expose] def amPhi2 {M₀ : Subgroup G}
    (φ : (RankTwoAmalgam.ofSubgroups M₀ H).Iso (RankTwoAmalgam.ofSubgroups U42.P1 U42.P2)) :
    ↥H ≃* ↥U42.P2 :=
  φ.φ2

end AS62

end CFSG.LargeExtraspecial
