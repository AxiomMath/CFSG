module

public import CFSG.Quasithin.H13.L32AL2Ia
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A705a

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace IData

variable {T L V TY : Subgroup G} {z z' : G} (D : IData T L V TY z z')
include D

theorem V_spec_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    IsElemAbelian 2 V ∧ Nat.card V = 8 := by
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V D.S.hyp.hyp D.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 D.S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 D.S.hyp h1222 h1332 h1334 hV2
  exact ⟨⟨inferInstance, fun v hv => S14.sq_V_F4 hv⟩, S14.card_V_F4⟩

theorem W0_ne_bot_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    E3.wClos V 0 TY ≠ ⊥ := by
  obtain ⟨hVe, hV8⟩ := D.V_spec_F4 h1222 h1332 h1334
  refine E3.wClos_ne_bot hVe D.hVTY ?_
  have : rk ↥V = 3 := by
    rw [rk, hV8, show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]
  omega

theorem pCoreOf_iI_ne_bot_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    pCoreOf 2 (iI T L V z z') ≠ ⊥ := by
  have hW := LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 D.W0_le_iI D.iI_le_normalizer_W0
    (D.isPGroup_T.to_le ((E3.wClos_le 0 TY).trans D.hTY))
  intro hb
  exact D.W0_ne_bot_F4 h1222 h1332 h1334 (le_bot_iff.mp (hb ▸ hW))

theorem charTwo_iI_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    CharTwo (iI T L V z z') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT := D.S.hyp.fsu.sylow
  refine charTwo_of_inH D.S.hyp.fsu.qtke.2.1 (hT.1.toSylow hT.2)
    ⟨?_, D.pCoreOf_iI_ne_bot_F4 h1222 h1332 h1334⟩
  rw [IsPGroup.toSylow_coe]
  exact T_le_iI

theorem sqtk_iI_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    SQTKGroup ↥(iI T L V z z') :=
  sqtkGroup_of_pCoreOf_ne_bot D.S.hyp.fsu.qtke D.S.hyp.fsu.simple D.S.hyp.fsu.nonabelian
    (D.pCoreOf_iI_ne_bot_F4 h1222 h1332 h1334)

theorem vI_spec_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    vI T L V z z' ≤ pCoreOf 2 (iI T L V z z') ⊓
        Subgroup.centralizer (pCoreOf 2 (iI T L V z z') : Set G) ∧
      IsElemAbelian 2 (vI T L V z z') ∧ IsTwoReducedIn (iI T L V z z') (vI T L V z z') :=
  conjClosure_isTwoReducedIn_of_charTwo D.isSylowTwoOf_T (D.charTwo_iI_F4 h1222 h1332 h1334)
    inf_le_right

theorem not_le_normalizer_l1_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) : ¬ iI T L V z z' ≤ Subgroup.normalizer (l1 T L V : Set G) := by
  intro hN
  obtain ⟨-, -, hred⟩ := D.vI_spec_F4 h1222 h1332 h1334
  have hD : pCoreOf 2 (l1 T L V) ≤ Subgroup.centralizer (vI T L V z z' : Set G) := by
    refine hred.2.2.2 _ ((pCoreOf_le 2 _).trans l1_le_iI)
      (hN.trans (normalizer_le_normalizer_pCoreOf 2 _)) fun d hd => ?_
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (l1 T L V) ⟨d, hd⟩
    refine ⟨k, ?_⟩
    have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [this]
    exact Subgroup.one_mem _
  exact D.hL1 ((hD.trans (D.centralizer_vI_le.trans inf_le_right)).trans
    (Subgroup.centralizer_le_normalizer _))

theorem a114Y_not_le_normalizer_l1_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) : ¬ a114Y z z' ≤ Subgroup.normalizer (l1 T L V : Set G) := by
  intro hY
  refine D.not_le_normalizer_l1_F4 h1222 h1332 h1334 (sup_le (sup_le ?_ ?_) hY)
  · exact Subgroup.le_normalizer
  · exact Setting147.T_le_N_l1_F4 D.S h1332

end IData

end CFSG.Quasithin.H13.L32A.L2
