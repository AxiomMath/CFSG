module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.A6Inputs13_3
public import CFSG.Quasithin.H13.A6S4Defs

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Input1379Six_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → ¬ IsHatA6 L → S.G1 ∈ S.Hz →
    IsElemAbelian 2 (conjClosure S.V3 S.G1) → IsElemAbelian 2 (conjClosure V S.G1)

end CFSG.Quasithin.H13.A6
