module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L14A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L14E6
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L14G2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L14Producers

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def Stmt13_3_14d_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V V₂ V₃ Lp : Subgroup G), Set14 G T L V V₂ V₃ Lp →
    pCoreOf 2 (A6.g1 T V) ≤ centralizer (V₂ : Set G) → StepD T V Lp

theorem stmt13_3_14_of_F4
    (h1332 : Stmt13_3_2_F4) (h1336 : A6.Stmt13_3_6_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56) (hF : A318Facts)
    (h1310 : Stmt13_3_10_F4) (hd : Stmt13_3_14d_F4) (hA6 : Set14ProducerA6_F4)
    (hL32 : Set14ProducerL32_F4) (hU33 : Set14ProducerU33_F4) : A6.Stmt13_3_14_F4 := by
  intro G _ _ T L V V₂ hH hV hzv hV2 hA5 hQ
  obtain ⟨V₃, Lp, S⟩ := exists_set14_of_producers_F4 h1332 hA6 hL32 hU33 hH hV hzv hV2 hA5
  obtain ⟨K, hD⟩ := S.exists_kData_F4 h1332 h1336 h37 h38 h39 hQ (hd G T L V V₂ V₃ Lp S hQ)
  have hg := S.stepG_F4 h1332 hC58 h317 h56 hQ hD
  rcases S.K_A5_or_L32_F4 h1332 hF h38 hD hg with h | h
  · exact S.false_of_A5_F4 h1332 h1310 hA5 hD hg h
  · exact S.not_L32 hD hg h

end CFSG.Quasithin.H13.U3
