module

public import CFSG.Quasithin.H13.U3S13472F
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S13472B
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S13472C
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1347P4G

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem s1347_two_F4 (hC137 : C137StatementFiveZ_F4)
    (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2_F4) (h1228 : Stmt12_2_8_F4)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56) (h135 : A6.Stmt13_3_5_F4)
    (h1345 : NQS134.Stmt13_4_5_F4) (hF : F6.TheoremF618Cat) (hBig : A5.FactF618Big)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂)
    (hK₂L : oTwoRes H₂ = l2Of S) (hii : Concl1347ii T H₁ H₂) {X : Subgroup G}
    (hX : InH (H₁ ⊔ H₂) X)
    (hXZ : X ⊓ centralizer (quasithinOmegaOneCenter T : Set G) = T) : X = H₁ ⊔ H₂ := by
  have hJ1 :=
    (s1347_four_F4 hC137 hedge h1332 h1228 hC58 h317 h56 h135 h1345 hF hBig S h hK₂L).2 hii
  obtain ⟨D⟩ := P2.exists_data2_F4 hedge h1332 h1228 hC58 h317 h56 h135 h1345 S h hii
  have hS := P2.settingX_of_F4 h37 h39 h1345 D hX hXZ
  obtain ⟨A, hA, hAC⟩ := P2.exists_A D hJ1
  by_cases hB : (A ⊓ centralizer (v0Of T H₁ H₂ : Set G)) ⊔ v0Of T H₁ H₂ ≤
      centralizer (conjClosure (quasithinOmegaOneCenter T) X : Set G)
  · exact P2.eq_H0_of D hS (P2.eq_V0_of_B D hS hA hAC hB)
  · exact (P2.false_of_not_B h56 D hS hA hAC hB).elim

theorem s1347_two_forall_F4 (hC137 : C137StatementFiveZ_F4)
    (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2_F4) (h1228 : Stmt12_2_8_F4)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56) (h135 : A6.Stmt13_3_5_F4)
    (h1345 : NQS134.Stmt13_4_5_F4) (hF : F6.TheoremF618Cat) (hBig : A5.FactF618Big)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G)
      (S : A6.Setting134 G T L V) (H₁ H₂ : Subgroup G), Hyp1347 T H₁ H₂ →
      oTwoRes H₂ = l2Of S → Concl1347ii T H₁ H₂ → ∀ X : Subgroup G, InH (H₁ ⊔ H₂) X →
        X ⊓ centralizer (quasithinOmegaOneCenter T : Set G) = T → X = H₁ ⊔ H₂ :=
  fun _ _ _ _ _ _ S _ _ h hK₂L hii _ hX hXZ =>
    s1347_two_F4 hC137 hedge h1332 h1228 hC58 h317 h56 h135 h1345 hF hBig h37 h39 S h hK₂L hii hX
      hXZ

end CFSG.Quasithin.H13.U3
