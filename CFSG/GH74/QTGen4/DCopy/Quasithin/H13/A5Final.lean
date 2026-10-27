module

public import CFSG.Quasithin.H13.A5Final
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Global
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1326
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1515c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Blueprint
open scoped commutatorElement

@[expose] def Stmt13_2_7_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (_ : Setting G T L V) (H : Subgroup G),
    IsHStar T (Subgroup.normalizer (L : Set G)) H →
      H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)

theorem input1336_of_F4 (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4) : Input1336_F4 := by
  intro G _ _ T L V S hle
  obtain ⟨-, -, ⟨H, hH⟩, -, -⟩ := (h331 G T S.h13.simple S.h13.nonabelian S.h13.qtke
    S.h13.sylow).2 L S.maximal S.isQuasisimple_L
  rw [S.conjClosure_L_T] at hH
  have hHZ := h1327 G T L V S H hH
  apply hH.2.1
  refine le_trans ?_ hle
  intro x hx
  have := Subgroup.mem_centralizer_iff.mp (hHZ hx) S.z S.z_mem_omegaOneCenter
  show x ∈ Subgroup.centralizer ({S.z} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact this.symm

theorem stmt13_6_1_of_ext_F4
    (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) (h311 : Theorem311Stmt) (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4) (hG248 : StmtG248)
    (h13518 : Input13518_F4) (h136 : Input136_F4) (hF431 : StmtF431U42) :
    Stmt13_6_1_F4 := by
  have h1323 := input1323Two_of_F4 h311 h1222
  have h1326 := input1326Two_of_F4 h1222 h517
  have h1336 := input1336_of_F4 h331 h1327
  exact stmt13_6_1_of_inputs_F4 h132two h132fsu h132A5 h1323 h1336
    (input13515_of_F4 h1323 h1326 h1336 VolI.stmtF956i hG248 VolI.stmtC113c) h13518 h136
    hF431

end CFSG.Quasithin.H13.A5
