module

public import CFSG.GH74.QTGen4.U42.AmalgamExtension
public import CFSG.GH74.QTGen4.Finite4

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model CFSG.Blueprint
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5

variable {G : Type} [Group G] [Finite G] {T L V H I : Subgroup G}

theorem prop_13_5_17_constructive (S : A5.Setting G T L V) (hH : H ∈ S.Hz)
    (D : Data13515 S H I) (hF431 : StmtF431U42) :
    LieModel G .PSU 4 2 1 ∨ LieModel G .PSL 4 3 1 := by
  have hamal := amalgam_U42_constructive S hH D
  have hHM : ¬ H ⊔ (L ⊔ T) ≤ Subgroup.normalizer (L : Set G) := fun h =>
    hH.2.2 (le_sup_left.trans h)
  have ho2 : pCoreOf 2 (H ⊔ (L ⊔ T)) = ⊥ := S.o2_eq_bot_of_not_le le_sup_right hHM
  have hzH : S.z ∈ H := by
    rw [D.H_eq]
    exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hzc : S.z ∈ centerOf (H ⊓ (L ⊔ T)) := by
    refine ⟨⟨hzH, le_sup_right (a := L) (S.V_le_T S.z_mem_V)⟩, ?_⟩
    show S.z ∈ Subgroup.centralizer ((H ⊓ (L ⊔ T) : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxG1 : x ∈ S.G1 := D.H_eq ▸ hx.1
    exact Subgroup.mem_centralizer_singleton_iff.mp hxG1
  have hCz : Subgroup.centralizer ({S.z} : Set G) ≤ H := by rw [D.H_eq]; rfl
  have hN1 : Subgroup.normalizer (centerOf (pCoreOf 2 H) : Set G) = H := by
    rw [D.center_QH, ← S.G1_eq_normalizer, D.H_eq]
  have hN2 : Subgroup.normalizer (centerOf (pCoreOf 2 (L ⊔ T)) : Set G) = L ⊔ T := by
    rw [D.V_eq]
    have hcV : centerOf V = V := le_antisymm inf_le_left (le_inf le_rfl
      (fun v hv => Subgroup.mem_centralizer_iff.2 fun w hw =>
        congrArg Subtype.val (S.elemAbelian_V.1.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)))
    rw [hcV]
    exact le_antisymm (S.NV_le_M.trans D.M_eq.le) S.reduced.2.1
  exact hF431 G S.h13.simple S.h13.nonabelian H (L ⊔ T) S.z hamal ho2 S.z_sq S.z_ne_one hzc hCz
    hN1 hN2


theorem prop_13_5_17_constructive_F4 {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]
    {T L V H I : Subgroup G} (S : A5.Setting G T L V) (hH : H ∈ S.Hz)
    (D : Data13515 S H I) (hF431 : StmtF431U42) :
    LieModel G .PSU 4 2 1 ∨ LieModel G .PSL 4 3 1 :=
  prop_13_5_17_constructive S hH D hF431

end CFSG.GH74.QTGen4.U42
