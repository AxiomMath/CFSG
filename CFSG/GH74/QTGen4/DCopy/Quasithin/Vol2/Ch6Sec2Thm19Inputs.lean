module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch6StatementsSec2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

@[expose] def Res6219S8_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G), Hyp6Sec2 G T M L V →
    let Z := quasithinOmegaOneCenter T
    let H := Subgroup.centralizer (Z : Set G)
    let U := conjClosure (ch6ZS T L V) H
    let ZU := centerOf U
    ch6ZS T L V < V ⊓ U → Z < ZU →
    ∀ l ∈ oTwoUpper (L ⊓ Subgroup.normalizer (ch6ZS T L V : Set G)), l ∉ H →
      let X := conjSubgroup U l ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)
      ∀ (A : Type) [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
        (B : LinearMap.BilinForm (ZMod 2) A) (β : ↥U →* Multiplicative A)
        (ρ : ↥H →* (A ≃ₗ[ZMod 2] A)), IsSymplecticRealization H U ZU A B β ρ →
        ¬ G11.G112Concl8S8 B ρ.range ((X.subgroupOf H).map ρ)

end CFSG.Quasithin.H13
