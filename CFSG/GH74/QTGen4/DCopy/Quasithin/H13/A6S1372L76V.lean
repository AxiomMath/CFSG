module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76L
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76P3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76U

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

theorem lem1376Full_of_F4 (hB : Lem1376L1K_F4) (h3 : Lem1376NThree_F4)
    (h5 : Lem1376Five_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13314 : Stmt13_3_14_F4)
    (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4) (h1337 : Stmt13_3_7_F4) : Lem1376Full_F4 := by
  intro G _ _ T L V S hNS hNU H hH hab _ K hK
  refine ⟨fun n hn hBN => S.lem1376_one_F4 hB h3 h37 h38 h13314 h13315 h1356two h1337 hNS hNU hH hab
      hK n hn hBN,
    S.lem1376_two_F4 hB h37 h38 h13314 h13315 h1356two hNS hNU hH hab hK,
    fun n hAN => S.lem1376_three_F4 hB h37 h38 h13314 h13315 h1356two h1337 hNS hNU hH hab hK n hAN,
    S.lem1376_extSq4_F4 hB h37 h38 h13314 h13315 h1356two hNS hNU hH hab hK,
    S.lem1376_four_F4 hB h37 h38 h13315 h1356two h1337 hNS hNU hH hab hK,
    fun n hSL => ?_, fun n hSp => ?_, fun n hG2 => ?_⟩
  · exact (h5 G T L V S hNS hNU H hH hab K hK (hB G T L V S hNS hNU H hH hab K hK
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hSL⟩)))))))).1 n hSL
  · exact (h5 G T L V S hNS hNU H hH hab K hK (hB G T L V S hNS hNU H hH hab K hK
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hSp⟩))))))))).2.1 n hSp
  · exact (h5 G T L V S hNS hNU H hH hab K hK (hB G T L V S hNS hNU H hH hab K hK
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, hG2⟩))))))))).2.2 n hG2

end CFSG.Quasithin.H13.A6
