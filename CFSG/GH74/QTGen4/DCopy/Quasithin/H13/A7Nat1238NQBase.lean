module

public import CFSG.Quasithin.H13.A7Nat1238NQBase
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL6

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin Subgroup

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem solvableRadical_le_centralizer_conjClosure_F4 (h3214 : Stmt3_2_14_F4) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hQ : QuasithinUnique.quasithinIsQTKECat G)
    {T K₀ : Subgroup G} (hT : quasithinIsSylowTwo T) (hK₀ : quasithinIsLocal T K₀)
    (hq : ¬ CFSG.IsQuasisimple (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)) :
    (CFSG.solvableRadical ↥K₀).map K₀.subtype ≤
      centralizer (conjClosure (quasithinOmegaOneCenter T) (K₀ ⊔ T) : Set G) :=
  (h3214 G T K₀ hs hnab hQ hT hK₀ hq).trans
    (centralizer_le (isTwoReducedIn_conjClosure_omega hQ hT hK₀).2)

end CFSG.Quasithin.H13.A7
