module

public import CFSG.Quasithin.H13.L32AL2Ib
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A705a

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace IData

variable {T L V TY : Subgroup G} {z z' : G} (D : IData T L V TY z z')
include D

theorem TY_le_normalizer_l0_F4 (h1332 : Stmt13_3_2_F4) :
    TY ≤ Subgroup.normalizer (l0 T L V z' : Set G) := fun _ ht =>
  mem_normalizer_inf (Setting147.T_le_N_l1_F4 D.S h1332 (D.hTY ht))
    (mem_normalizer_centralizer (D.hTYV ht))

theorem pCoreOf_a114Y_le_normalizer_l0_F4 (h1332 : Stmt13_3_2_F4) :
    pCoreOf 2 (a114Y z z') ≤ Subgroup.normalizer (l0 T L V z' : Set G) :=
  D.hO2Y0.trans (D.TY_le_normalizer_l0_F4 h1332)

theorem a114Y_le_normalizer_l0_sup_F4 (h1332 : Stmt13_3_2_F4) :
    a114Y z z' ≤ Subgroup.normalizer ((l0 T L V z' ⊔ pCoreOf 2 (a114Y z z') : Subgroup G) :
      Set G) := by
  obtain ⟨-, -, hcomm, -⟩ := a114_three D.hA
  have hQN := D.pCoreOf_a114Y_le_normalizer_l0_F4 h1332
  refine le_normalizer_of_conj fun y hy k hk => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hQN).1 hk
  have hya : y * a * y⁻¹ * a⁻¹ ∈ pCoreOf 2 (a114Y z z') :=
    hcomm (Subgroup.commutator_mem_commutator hy (Subgroup.mem_inf.mp ha).2)
  have hyb : y * b * y⁻¹ ∈ pCoreOf 2 (a114Y z z') :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hy) b).mp hb
  have e : y * (a * b) * y⁻¹ = (y * a * y⁻¹ * a⁻¹) * a * (y * b * y⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hya)
    (Subgroup.mem_sup_left ha)) (Subgroup.mem_sup_right hyb)

theorem oTwoUpper_l0_sup_F4 (h1332 : Stmt13_3_2_F4) :
    oTwoUpper (l0 T L V z' ⊔ pCoreOf 2 (a114Y z z')) = lY T L V z' := by
  refine le_antisymm ?_ (oTwoUpper_mono le_sup_left)
  have h1 := L32A.oTwoUpper_sup_le_of_two (pCoreOf_isPGroup 2 (a114Y z z'))
    (D.pCoreOf_a114Y_le_normalizer_l0_F4 h1332)
  rw [oTwoUpper, Subgroup.closure_le]
  rintro x ⟨hx, ho⟩
  exact mem_oTwoUpper_of_odd (h1 (mem_oTwoUpper_of_odd hx ho)) ho

theorem a114Y_le_normalizer_lY_F4 (h1332 : Stmt13_3_2_F4) :
    a114Y z z' ≤ Subgroup.normalizer (lY T L V z' : Set G) := by
  have h := (D.a114Y_le_normalizer_l0_sup_F4 h1332).trans
    (normalizer_le_normalizer_oTwoUpper (l0 T L V z' ⊔ pCoreOf 2 (a114Y z z')))
  rwa [D.oTwoUpper_l0_sup_F4 h1332] at h

end IData

end CFSG.Quasithin.H13.L32A.L2
