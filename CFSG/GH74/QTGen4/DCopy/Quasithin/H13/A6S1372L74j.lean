module

public import CFSG.Quasithin.H13.A6S1372L74j
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L74a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L74i
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3C137

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

theorem lem1374OneDiag_of_F4 (h1227 : U3.Stmt13_2_2_7_F4)
    (h1337 : Stmt13_3_7_F4) : Lem1374OneDiag_F4 := by
  intro G _ _ T L V S _ _ hhat H hH _ hB K hKc hHK h52 hL1K hc
  have hKH : K ≤ H := le_of_mem_cComp hKc
  obtain ⟨x, hxN, hxL, hx3, hx1⟩ := Setting4.exists_L1_act_ne_one hhat hH hHK hc
  obtain ⟨k, hkK, hk3, hk1, m, hkm⟩ := A6L74.exists_cube_act h52 hxN hx3 hx1
  have hXN : S.L1 ⊔ T ≤ Subgroup.normalizer (K : Set G) := hH.1.1.trans hHK
  have hxm : x ^ m ∈ S.L1 ⊔ T := (S.L1 ⊔ T).pow_mem (Subgroup.mem_sup_left hxL) m
  have hkR := A6L74.mem_normalizer_pCoreOf_of_act (A6L74.center_eq_bot_of h52) hXN le_sup_right
    S.h13.sylow hkK hxm (hkm _ _)
  have hRM : Subgroup.normalizer (pCoreOf 2 (S.L1 ⊔ T) : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
    rcases h1227 G T L V S.L1 S.h13 S.irr S.zv (fun h => absurd h hhat) (fun _ => rfl) S.a6
      with h | h
    · exact S.normalizer_R1_le_M h
    · exact absurd h hB
  exact hk1 (Setting4.eq_one_of_cube_of_mem_M_F4 hH h1337 hhat hKH hHK hL1K hkK hk3 (hRM hkR))

end CFSG.Quasithin.H13.A6
