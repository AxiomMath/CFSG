module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3C137
public import CFSG.Quasithin.H13.A6S1372L74k

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

theorem not_thompsonJ_le_of_eq_F4 (h1227 : U3.Stmt13_2_2_7_F4) (hhat : ¬ IsHatA6 L)
    (hB : ¬ H13.IsA6Block L) {K : Subgroup G} (hKM : ¬ K ≤ Subgroup.normalizer (L : Set G))
    {U : Subgroup G} (hUe : IsElemAbelian 2 U) (hUR : U ≤ pCoreOf 2 (S.L1 ⊔ T))
    (hRC : pCoreOf 2 (S.L1 ⊔ T) ⊓ Subgroup.centralizer (U : Set G) =
      pCoreOf 2 (K ⊔ pCoreOf 2 (S.L1 ⊔ T))) :
    ¬ thompsonJ (pCoreOf 2 (S.L1 ⊔ T)) ≤ Subgroup.centralizer (U : Set G) := by
  intro hJ
  have hbaum : baum (pCoreOf 2 (S.L1 ⊔ T)) = baum (pCoreOf 2 (K ⊔ pCoreOf 2 (S.L1 ⊔ T))) := by
    rw [← hRC]
    exact baum_eq_baum_centralizer hUe hUR (le_inf (thompsonJ_le_self _) hJ)
  have hRM : Subgroup.normalizer (baum (pCoreOf 2 (S.L1 ⊔ T)) : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
    rcases h1227 G T L V S.L1 S.h13 S.irr S.zv (fun h => absurd h hhat) (fun _ => rfl) S.a6
      with h | h
    · exact normalizer_baum_R1_le_M h
    · exact absurd h hB
  apply hKM
  intro k hk
  apply hRM
  rw [hbaum]
  exact normalizer_le_normalizer_baum _ (le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hk))

end Setting4

end CFSG.Quasithin.H13.A6
