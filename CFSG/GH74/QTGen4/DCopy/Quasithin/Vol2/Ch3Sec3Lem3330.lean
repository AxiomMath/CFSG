module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3StatementsB
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3328Pre
public import CFSG.Quasithin.Vol2.Ch3Sec3Sec

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Lem3328
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

@[expose] def Stmt3_3_28G2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsG2Block L → tC L T = ⊥ ∧ qL L T = vPlus L T

@[expose] def Stmt3_3_28G2TC_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsG2Block L → tC L T = ⊥

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L D : Subgroup G}

theorem stmt3_3_28G2_of_F4 (h25 : Stmt3_3_25_F4) (hTC : Stmt3_3_28G2TC_F4) : Stmt3_3_28G2_F4 := by
  intro G _ _ T M L D h hG2
  have hTC' := hTC G T M L D h hG2
  refine ⟨hTC', ?_⟩
  rcases (h25 G T M L D h).2.2 hTC' with hV | hA6
  · exact hV.symm
  · exfalso
    obtain ⟨-, α, hαs, hαk, -⟩ := hA6
    have h1 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 6048 := F420.card_of_u33 hG2.2.1
    have h2 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 := by
      rw [← hαk, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαs).toEquiv,
        nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    omega

end CFSG.Quasithin.H13
