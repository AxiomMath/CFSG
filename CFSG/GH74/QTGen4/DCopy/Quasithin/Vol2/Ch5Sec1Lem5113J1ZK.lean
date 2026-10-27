module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113J1Seven
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113Mod
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113J1ZKS331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped MatrixGroups

theorem stmt5_1_13_type_j1_ZK_of_F4 (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h510 : Stmt5_1_10_F4) (h513 : Stmt5_1_3_F4)
    (h432 : Stmt4_3_2_F4) : Stmt5_1_13_type_j1_ZK_F4 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 hcl hJ h7 hn3 hZK
  have h := m.hyp.toHyp5_0_1
  set Z := quasithinOmegaOneCenter T with hZdef
  have hKhZ : Kh₁ ≤ Subgroup.centralizer (Z : Set G) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZK)
  obtain ⟨y, hyD, hyK, hy1, hy7⟩ := m.exists_seven_F4 h37 h38 h510 hc5 hcl hJ h7 hn3

  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf m.hyp.hStar.1.1
  have hKT : oTwoUpper H ⊔ T = H := by
    rw [sup_comm, ← F6.twoResidual_eq_oTwoUpper]
    exact sup_twoResidual_eq hTH
  have hKZ : oTwoUpper H ≤ Subgroup.centralizer (Z : Set G) :=
    (m.lt.le.trans hcl.le).trans hKhZ
  have hHZ : H ≤ Subgroup.centralizer (Z : Set G) :=
    hKT ▸ sup_le hKZ (Main513.T_le_centralizer_omega T)
  exact h.false_of_seven_F4 h513 m.module m.nota.2.1 (m.inf_centralizer_eq_bot_F4 h432 hHZ) hyD hy1
    hy7 (hKhZ hyK)

end CFSG.Quasithin.H13
