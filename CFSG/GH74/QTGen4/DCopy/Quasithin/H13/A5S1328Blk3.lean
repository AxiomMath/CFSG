module

public import CFSG.Quasithin.H13.A5S1328Blk3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5RawNat
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327v
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1328Blk2
public import CFSG.GH74.QTGen4.A5.Res1328Gen4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L1332

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem exists_setting_cComp_F4 (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) {H K : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) (hKc : K ∈ cComp H)
    (hHK : H = K ⊔ T) : ∃ VH : Subgroup G, Nonempty (Setting G T K VH) := by
  have hZK : ⁅quasithinOmegaOneCenter T, K⁆ ≠ ⊥ := by
    intro h
    apply hHZ
    rw [hHK]
    refine sup_le ?_ (T_le_centralizer_omegaOneCenter T)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact h)
  have hKloc : quasithinIsLocal T K :=
    ⟨S.isPGroup_T, cComp_subset_lFamily hH.1.1 hKc,
      (isSylowTwoOf_of_le S.h13.sylow le_sup_right).2.2, by rw [← hHK]; exact hH.1.2⟩
  have hKf : quasithinIsFaithfulLocal T K :=
    Vol2.Ch11.SecS.isFaithfulLocal_of_omegaOneCenter S.h13.qtke S.h13.sylow hKloc hZK
  exact exists_setting_F4 h132two h132fsu h132A5 (QTH13.of_faithful S.h13 S.a5 hKf)
    (S.h13.a5 S.a5 K hKf)

end Setting

theorem res1328a_of_F4 (h132two : Stmt13_3_2_two_F4)
    (h132fsu : Stmt13_3_2_three_fsu_F4) (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4)
    (h512 : Stmt5_1_2_F4) (h5172 : Stmt5_1_7_two_F4) (h126 : TheoremC126) :
    Res1328a_F4 := by
  intro G _ _ T L V S H K hH hHZ hKc hHK _ _
  have hZK := CFSG.GH74.QTGen4.A5.res1328aSym_finite4 S hH hHZ hKc hHK
  obtain ⟨VH, ⟨S'⟩⟩ := S.exists_setting_cComp_F4 h132two h132fsu h132A5 hH hHZ hKc hHK
  have hO := S.pCoreOf_KT_eq_F4 h331 h512 h5172 h126 S' hH hHZ hHK hZK
  refine S'.rootFourLiftQuot_of ?_
  rw [S'.cT, hO]

theorem stmt13_2_7_of_caseS2A_c126_F4
    (h331 : Stmt3_3_1_F4) (h311 : Theorem311Stmt) (h432 : Stmt4_3_2_F4) (h523 : Stmt5_2_3_F4)
    (h1222 : Stmt12_2_2_F4) (h5172 : Stmt5_1_7_two_F4) (hE22 : E2.E22StatementNoN)
    (hF618 : F6.TheoremF618Cat) (hBig : FactF618Big) (hL2 : FactL2Three) (h1332 : Stmt13_3_2_F4)
    (h512 : Stmt5_1_2_F4) (h137 : EmptyFaithfulMultiple.Input137)
    (h126 : TheoremC126) (hA : CaseS2A_1327_F4) : Stmt13_2_7_F4 :=
  stmt13_2_7_of_caseS2A_ofNoN_F4 h331 h311 h432 h523 h1222 h5172 hE22
    (res1328a_of_F4 (stmt13_3_2_two_of_F4 h1332) (stmt13_3_2_three_fsu_of_F4 h1332)
      (stmt13_3_2_three_A5_of_F4 h1332) h331 h512 h5172 h126)
    hF618 hBig hL2 h1332 h512 h137 hA

end CFSG.Quasithin.H13.A5
