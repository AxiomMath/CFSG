module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtC137U33Pt3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtC137U33Stmt
public import CFSG.Quasithin.H13.GoldschmidtC137U33Ln

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem c137CaseU33R_of_F4 (hI : B5.B51IrrInputs) (hA21 : AsA21SQTKSection)
    (hA36 : AsA36NoOddCover) (hcov : G2NaturalCover) (hnorm : G2DerivedNormalizerZorn)
    (hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32_F4) (hfacts : U33G2Facts) : C137CaseU33R_F4 := by
  intro G _ _ X T V L P M hC hSQ hT hprod hL hL2 hlie hTP hPM hMX hmax hPeq hred hVL hV0
  have h : U33Cfg X T V L P M :=
    ⟨hSQ, hC, hT, hprod, hL, hL2, hlie, hTP, hPM, hMX, hmax, hPeq, hred, hVL, hV0⟩
  rcases entry33_or_concl1 hI hA21 hA36 hC hSQ hred hT hprod hL hL2 h.hVL' hlie h.toBaum.hQR
      h.toBaum.hRT with ⟨C, hC0, hCle, hCchar, hCn⟩ | E
  · exact Or.inl ⟨C, hCle, hC0, hCchar, hCn⟩
  · have hF := g2Facts_of_entry33 hcov hnorm hfacts E hVL
    rcases hF.dichotomy _ _ h.sylow_T h.T_le_P h.P_le_X h.P_ne_X h.P_max with hl | hp
    · exact Or.inr (Or.inr (Or.inl (h.concl4_of_line hF hl)))
    · by_cases hcn : CharNormal (baum (pCoreOf 2 P)) X
      · exact Or.inl hcn
      · obtain ⟨A, hA, c, hc, hLc⟩ := hp.exists_PtA
        exact Or.inr (Or.inl (h.blockPart_of_point_F4 E hF hA hc hLc hC132
          fun C hCle hC0 hchar hXC => hcn ⟨C, hCle, hC0, hchar, hXC⟩))

theorem c137CaseU33_of_F4 (hI : B5.B51IrrInputs) (hA21 : AsA21SQTKSection)
    (hA36 : AsA36NoOddCover) (hcov : G2NaturalCover) (hnorm : G2DerivedNormalizerZorn)
    (hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32_F4) (hfacts : U33G2Facts) : C137CaseU33_F4 :=
  c137CaseU33_of_R_F4 (c137CaseU33R_of_F4 hI hA21 hA36 hcov hnorm hC132 hfacts)

end CFSG.Quasithin.H13.U3.GC137
