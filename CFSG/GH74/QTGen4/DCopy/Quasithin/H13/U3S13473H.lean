module

public import CFSG.Quasithin.H13.U3S13473H
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S13473F

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem s1347_three_F4 (hns : Stmt13473NonSolv_F4)
    (hF : F6.TheoremF618Cat) (hBig : A5.FactF618Big) (hedge : GoldschmidtEdgeBoundS3)
    (h1332 : Stmt13_3_2_F4) (h1228 : Stmt12_2_8_F4) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (h135 : A6.Stmt13_3_5_F4) (h1222 : Stmt12_2_2_F4) (h139 : A6.Stmt13_3_9_F4)
    (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂)
    (hK₂L : oTwoRes H₂ = l2Of S) : ¬ Concl1347iii T H₁ H₂ := by
  intro hiii
  obtain ⟨Y₂, Y, D⟩ :=
    exists_data13473_F4 hedge h1332 h1228 hC58 h317 h56 h135 h1222 h139 S h hK₂L hiii
  obtain ⟨-, -, -, -, -, hc₁, -⟩ := s1347_one_first_F4 hedge h1332 h1228 hC58 h317 h56 h135 S h
  have hZ4 : Nat.card ↥(quasithinOmegaOneCenter T) = 4 := by rw [h.index₁, hc₁]
  exact D.not_isSolvable hF hBig hZ4 (D.isSolvable_F4 hns h hK₂L hiii)

end CFSG.Quasithin.H13.U3
