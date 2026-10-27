module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32A727a

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Input14727B2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ X : Subgroup ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)), IsSupercritical 3 X →
      (∀ α : MulAut ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)), (orderOf α).Coprime 3 →
        (∀ x ∈ X, x⁻¹ * α x ∈ frattiniIn X) → α = 1) →
      ¬ L32A.R727.pre H (X.map (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).subtype) ≤
        Subgroup.normalizer (L : Set G) →
      H = L32A.R727.pre H (X.map (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).subtype) ⊔
        (L32A.l1 T L V ⊔ T) →
      modO2Image H (L32A.l1 T L V) ≤ CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)

end CFSG.Quasithin.H13
