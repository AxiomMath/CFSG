module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Steps

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Stmt5_1_13_c2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → K₁ < oTwoUpper H → LieModel (O2Q K₁) .PSL 2 2 2 →
    (IsSporadic .J1 (O2Q Kh₁) ∨
      ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ IsPSL 2 p 1 (O2Q Kh₁)) →
    False

end CFSG.Quasithin.H13
