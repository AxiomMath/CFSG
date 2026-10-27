module

public import CFSG.Quasithin.H13.A5Y1367b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5X1367d

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem isSylowTwoOf_Tv_HK_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) {K : Subgroup G}
    (hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G)) : IsSylowTwoOf S.Tv (S.HK K) := by
  have hsyl := S.isSylowTwoOf_Tv_F4 h1222 h517
  refine ⟨S.Tv_le_HK K, hsyl.2.1, fun h2 => hsyl.2.2 ?_⟩
  have hrel := Subgroup.relIndex_mul_relIndex S.Tv (S.HK K) _ (S.Tv_le_HK K) (S.HK_le_Gv hKG)
  have h' : 2 ∣ S.Tv.relIndex (S.HK K) := h2
  have h3 : 2 ∣ S.Tv.relIndex (Subgroup.centralizer ({S.v12} : Set G)) :=
    hrel ▸ dvd_mul_of_dvd_left h' _
  exact h3

theorem charTwo_HK_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G)) : CharTwo (S.HK K) :=
  S153D.charTwo_of_le hF (S.HK_le_Gv hKG)
    ((pCoreOf_two_le_of_isSylowTwoOf (S.isSylowTwoOf_Tv_F4 h1222 h517)).trans (S.Tv_le_HK K))

theorem isTwoReducedIn_WK_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) : IsTwoReducedIn (S.HK K) (S.WK K) := by
  have hsyl := S.isSylowTwoOf_Tv_HK_F4 h1222 h517 hKG
  rw [S.WK_eq hT]
  exact isTwoReducedIn_conjClosure_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2
    (S.charTwo_HK_F4 h1222 h517 hF hKG) S.V1_le_omega_Tv

theorem WK_le_Tv_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) :
    S.WK K ≤ S.Tv ∧ pCoreOf 2 (S.HK K) ≠ ⊥ := by
  have hsyl := S.isSylowTwoOf_Tv_HK_F4 h1222 h517 hKG
  obtain ⟨hWc, -⟩ := conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2
    (S.charTwo_HK_F4 h1222 h517 hF hKG) S.V1_le_omega_Tv
  rw [← S.WK_eq hT] at hWc
  refine ⟨hWc.trans (inf_le_left.trans (pCoreOf_two_le_of_isSylowTwoOf hsyl)), fun h => ?_⟩
  have hz : S.z ∈ pCoreOf 2 (S.HK K) := (hWc (le_conjClosure _ _ (Subgroup.mem_zpowers _))).1
  rw [h, Subgroup.mem_bot] at hz
  exact S.z_ne_one hz

theorem sqtkGroup_HK_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) : SQTKGroup ↥(S.HK K) :=
  sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian
    (S.WK_le_Tv_F4 h1222 h517 hF hKG hT).2

end Setting

end CFSG.Quasithin.H13.A5
