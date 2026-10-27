module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.A5S1327b

public section
namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Lemma13213_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting G T L V) (H : Subgroup G),
    IsHStar T (Subgroup.normalizer (L : Set G)) H →
    ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) → Group.IsSolvable ↥H →
    Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)) → ¬ ThreeTop (S.H0 H)

end CFSG.Quasithin.H13.A5
