module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A74
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L134
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L15L

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem lemma14_7_4_two_three_of_F4
    (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h13314 : A6.Stmt13_3_14_F4) : Lemma14_7_4_two_three_F4 := by
  intro G _ _ T L V V₂ h hV2
  have h1334 : A6.Stmt13_3_4_F4 := U3.stmt13_3_4_of_F4 h1332
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14_F4 h1222 h1332 h1334 hV2
  obtain ⟨hN, hI, -, hS3, hO2, -, -, h3, -⟩ := U3.u3Stmt13_3_15_of_L32_F4 h1332 h13314 S14.hH
    S14.hlin S14.hnat S14.hV S14.hZV hV2 rfl rfl
  have hTG1 : T ≤ A6.g1 T V := (h.isTSub_V1_F4 hMod).2.2
  have hO : pCoreOf 2 (A6.g1 T V) ≤ T := pCoreOf_le_of_le h hTG1
  have hL2 : L₁Of L V₂ ≤ Subgroup.normalizer (V₂ : Set G) :=
    (oTwoRes_le _).trans inf_le_right
  have hI' : i2 T V V₂ = L₁Of L V₂ ⊔ pCoreOf 2 (A6.g1 T V) := hI
  refine ⟨⟨?_, hN⟩, hI, hS3, hO2.symm, h3⟩
  rw [hI']
  exact sup_le hL2 (hO.trans hV2.2.2.1)

end CFSG.Quasithin.H13.L32A
