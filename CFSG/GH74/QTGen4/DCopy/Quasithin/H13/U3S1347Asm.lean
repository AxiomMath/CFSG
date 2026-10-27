module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S13473H
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1347P4G
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1347St
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1347Z6

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

theorem stmt13_4_7L2_of_F4 (hC137 : C137StatementFiveZ_F4)
    (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2_F4) (h1228 : Stmt12_2_8_F4)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56) (h135 : A6.Stmt13_3_5_F4)
    (h1345 : NQS134.Stmt13_4_5_F4) (hF : F6.TheoremF618Cat) (hBig : A5.FactF618Big)
    (h1222 : Stmt12_2_2_F4) (h139 : A6.Stmt13_3_9_F4) (hns : Stmt13473NonSolv_F4)
    (htwo : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G)
      (S : A6.Setting134 G T L V) (H₁ H₂ : Subgroup G), Hyp1347 T H₁ H₂ →
      oTwoRes H₂ = l2Of S → Concl1347ii T H₁ H₂ → ∀ X : Subgroup G, InH (H₁ ⊔ H₂) X →
        X ⊓ centralizer (quasithinOmegaOneCenter T : Set G) = T → X = H₁ ⊔ H₂) :
    Stmt13_4_7L2_F4 := by
  intro G _ _ T L V S H₁ H₂ h hK₂L
  have h4 := s1347_four_F4 hC137 hedge h1332 h1228 hC58 h317 h56 h135 h1345 hF hBig S h hK₂L
  exact ⟨s1347_one_F4 hedge h1332 h1228 hC58 h317 h56 h135 h1345 hF hBig S h,
    htwo G T L V S H₁ H₂ h hK₂L,
    s1347_three_F4 hns hF hBig hedge h1332 h1228 hC58 h317 h56 h135 h1222 h139 S h hK₂L, h4.1, h4.2⟩

end CFSG.Quasithin.H13.U3
