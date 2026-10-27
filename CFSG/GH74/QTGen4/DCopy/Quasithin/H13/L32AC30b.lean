module

public import CFSG.Quasithin.H13.L32AC30b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A74
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC30a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk5

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem relIndex_l1_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h : Hyp147 G T L V) : (pCoreOf 2 (l1 T L V)).relIndex (l1 T L V) = 3 := by
  have h13322 := stmt13_3_2_two_of_F4 h1332
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨V₂, hV2⟩ := h.exists_V2_F4 h13322 hMod h1222
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have e : l1 T L V = L₁Of L (fsuV1 T V) := by rw [L₁Of, oTwoRes_eq_oTwoUpper]
  rw [e]
  exact (h.set14_F4 h1222 h1332 h1334 hV2).Lp3_F4

theorem hypF918_of_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h28 : Lemma14_7_28_F4) (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H)
    (S' : Setting147 G T L V (conjClosure K T ⊔ (l1 T L V ⊔ T))) :
    HypF918 T V L (fsuV1 T V) V (conjClosure K T ⊔ (l1 T L V ⊔ T)) K := by
  have h13322 := stmt13_3_2_two_of_F4 h1332
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have hF := L1286.hypF98_of_abelian_F4 h1222 h37 h38 h39 (S'.hyp.hyp1281One_F4 h13322 hMod)
    (S'.hyp.isTSub_V1_F4 hMod) S'.hyp.abelian S'.hz
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hK0H : conjClosure K T ≤ H := conjClosure_le fun t ht k hk =>
    H.mul_mem (H.mul_mem (hTH ht) (hKH hk)) (H.inv_mem (hTH ht))
  have hH'H : conjClosure K T ⊔ (l1 T L V ⊔ T) ≤ H := sup_le hK0H S.hz.1.1
  have hKH' : K ≤ conjClosure K T ⊔ (l1 T L V ⊔ T) := (le_conjClosure K T).trans le_sup_left
  have hl1L : l1 T L V ≤ L := (oTwoUpper_le _).trans inf_le_left
  refine ⟨hF, cComp_mem_of_le hK hKH' hH'H,
    isQuasisimple_cStar_F4 h36 h28 S (relIndex_l1_F4 h1222 h1332 h1334 S.hyp) hK, ?_,
    hH'H.trans (le_normalizer_conjClosure_T h37 h38 S hK)⟩
  exact le_antisymm (sup_le le_sup_left (le_sup_of_le_right
    (le_inf (sup_le_sup_right hl1L T) le_sup_right))) (sup_le le_sup_left inf_le_right)

theorem lemma14_7_30_of_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h28 : Lemma14_7_28_F4) (h519 : Lemma14_5_19_F4) : Lemma14_7_30_F4 := by
  intro G _ _ T L V H S K hK
  obtain ⟨hnot, S'⟩ := h519 G T L V H S K hK
  exact ⟨isQuasisimple_cStar_F4 h36 h28 S (relIndex_l1_F4 h1222 h1332 h1334 S.hyp) hK, hnot, S',
    hypF918_of_F4 h1222 h1332 h1334 h36 h37 h38 h39 h28 S hK S'⟩

end CFSG.Quasithin.H13.L32A.C
