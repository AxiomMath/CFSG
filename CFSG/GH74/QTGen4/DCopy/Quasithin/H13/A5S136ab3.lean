module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136o
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem exists_conf1366_Lv_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    {K : Subgroup G} (hK : IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G)))
    (hinner : Ch1.InducesInner S.z K) :
    ∃ (X Q : Subgroup G) (y : G), y ∈ S.Lv ∧ Conf1366 K X Q S.a S.z y := by
  obtain ⟨X, Q, y₀, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, -, -, -, -⟩ :=
    S.exists_conf1366_F4 h1222 h517 h37 h38 hK hinner
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  obtain ⟨-, -, hzM, -⟩ := (S.lemma115Hyp_Gv_F4 h1222 h517).component_action hK
  have hzK : ¬ K ≤ Subgroup.centralizer ({S.z} : Set G) := hzM
  have hKG : K ≤ Gv := hK.1
  have hKc : K ∈ cComp Gv := by
    have h2 := map_subtype_mem_cComp (mem_cComp_top_of_isComponent hK.2)
    rwa [Subgroup.map_subgroupOf_eq_of_le hKG] at h2
  have hLvN := S.Lv_le_normalizer_of_mem_cComp_F4 h1222 h517 h37 h38 hKc
  obtain ⟨y, hyLv, hyodd, hyz⟩ := S.exists_Lv_odd hKG hLvN hzK
  refine ⟨X, Q, y, hyLv, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hLvN hyLv,
    hyodd, ?_, hyz⟩
  rw [S.Lv_comm_a hyLv, mul_inv_cancel]
  exact Subgroup.one_mem _

end Setting

end CFSG.Quasithin.H13.A5
