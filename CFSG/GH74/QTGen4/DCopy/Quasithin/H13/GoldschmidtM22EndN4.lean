module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN4b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN4f

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

theorem endN4_F4 (hG : G64Out) (h621 : Stmt6_2_1_F4) (h622 : Stmt6_2_2_F4)
    (h626 : Stmt6_2_6_F4) (h629 : Stmt6_2_9_F4) (h6210 : Stmt6_2_10_F4) (h6211 : Stmt6_2_11_F4)
    (h6212 : Stmt6_2_12_F4) (h6110 : Stmt6_1_10_F4) (h : Hyp6Sec2 G T M L V)
    (hZS : ch6ZS T L V = V ⊓ UU T L V) :
    ∃ (g : G) (D : Subgroup G), KData T L V g D ∧
      (∀ q ∈ Subgroup.centralizer (V : Set G), ∃ v ∈ V,
        ∃ c ∈ Subgroup.centralizer (D : Set G) ⊓ CHU T L V, q = v * c) ∧
      Subgroup.centralizer (D : Set G) ⊓ CHU T L V ≤ Subgroup.centralizer (V : Set G) ∧
      Subgroup.centralizer (D : Set G) ⊓ HH T ≤ CHU T L V ∧
      Subgroup.normalizer (V : Set G) = L ⊔ T ∧ Subgroup.centralizer (V : Set G) ≤ T ∧
      pCoreOf 2 (Subgroup.normalizer (V : Set G)) = Subgroup.centralizer (V : Set G) ∧
      oTwoUpper (Subgroup.normalizer (V : Set G)) = L := by
  have hZ : Nat.card (quasithinOmegaOneCenter T) = 2 := (h622 G T M L V h).2.1
  obtain ⟨P⟩ := endN2_F4 hG h621 h622 h626 h629 h6210 h6211 h6212 h hZS
  obtain ⟨g, D, hk⟩ := endN3_F4 hG h621 h622 h626 h629 h6210 h6211 h6212 h hZS
  exact ⟨g, D, hk,
    fun q hq => hk.exists_mul_of_mem_centralizer_V_F4 h P hZ h621 h629 h6110 h6210 h6211 h6212 hq,
    hk.centralizer_inf_CHU_le_centralizer_V_F4 h h6110 h6211 h6212,
    hk.centralizer_inf_HH_le_CHU_F4 h P hZ h621 h629 h6110 h6210 h6211 h6212,
    P.normalizer_eq_sup_F4 h hZ h621 h629 h6210 h6212,
    P.centralizer_le_T_F4 h hZ h621 h629 h6210 h6212,
    P.pCoreOf_normalizer_eq_F4 h hZ h621 h629 h6210 h6212,
    P.oTwoUpper_normalizer_eq_F4 h hZ h621 h629 h6210 h6212⟩

end CFSG.Quasithin.H13.GM22
