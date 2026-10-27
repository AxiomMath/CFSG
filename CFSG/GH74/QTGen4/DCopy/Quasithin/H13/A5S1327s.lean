module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327q
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem H0_le_normalizer_oTwoUpper_F4 (h331 : Stmt3_3_1_F4)
    (h1222 : Stmt12_2_2_F4) (h5172 : Stmt5_1_7_two_F4) (h1332 : Stmt13_3_2_F4)
    (h137 : EmptyFaithfulMultiple.Input137) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : ¬ Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (hO2 : pCoreOf 2 (S.H0 H) ≠ ⊥) :
    S.H0 H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  have hXi := S.isXiStar_oTwoUpper_F4 h331 h1222 h5172 h1332 hH hHZ hsolv hS3
  have hU := h137 G T S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow _ hXi
  obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
    (⟨pCoreOf 2 (S.H0 H), hO2, pCoreOf_isPGroup 2 _, rfl⟩ :
      IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (S.H0 H) : Set G)))
  have hH0M' : S.H0 H ≤ M' := (le_normalizer_pCoreOf 2 _).trans hM'le
  have hHH0 : H ≤ S.H0 H := le_sup_right
  have hXT : oTwoUpper H ⊔ T ≤ M' :=
    (sup_le (oTwoUpper_le H) hH.1.1).trans (hHH0.trans hH0M')
  rw [← hU.2 M' ⟨hM', hXT⟩]
  exact hH0M'

end Setting

end CFSG.Quasithin.H13.A5
