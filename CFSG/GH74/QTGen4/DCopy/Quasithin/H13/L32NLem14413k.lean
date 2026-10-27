module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems144c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14410b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14411f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14413j
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLemE8b

public section

namespace CFSG.Quasithin.H13.L14413

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin


theorem y1444Claim_of_inputs_F4 (h1442 : Lemma1442Big_F4) (h1449 : Lemma1449Big_F4)
    (hA5 : Lemma14410A5_F4) (hM22 : Lemma14413BigM22_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h12811 : Lemma12_8_11_F4)
    (h12811h : Lemma12_8_11_hat_F4) (h12812 : Lemma12_8_12_two_F4) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
      CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V) → Nat.card ↥(fsuU T V) ≠ 2 ^ 5 →
      ∀ (V₂ : Subgroup G) (g : G), IsL32NPlane T V V₂ → g ∈ p128 T L V → g ∉ l32nH T V →
        Y1444Claim T L V V₂ g := by
  intro G _ _ T L V h hext hU V₂ g hV₂ hgP hgH
  have hs := h.setting1282One_F4 (stmt13_3_2_two_of_stmt13_3_2_F4 h1332)
    (stmtL32NModule_of_inputs_F4 h1332 h1334) hV₂
  obtain ⟨D⟩ := hs.exists_hatModelU_F4 h1222 h12213
  rcases h1442 G T L V h hext hU V₂ g hV₂ hgP hgH D with h3 | h4 | h8 | h5 | h6
  · exact (h1449 G T L V h hext hU V₂ g hV₂ hgP hgH D h3).elim
  · exact L14411.y1444Claim_of_case4_F4 h1332 h1334 h1222 h12213 h12811 h12812 h37 h38 h39 h hext
      hV₂ hgP hgH h4
  · exact (L1442E8.false_of_case1442EightPrime_F4 h1332 h1334 h1222 h12213 h12811 h12811h h12812 h37
      h38 h39 h hext hV₂ hgP hgH h8).elim
  · exact L14410.y1444Claim_of_case5_F4 hA5 h1332 h1334 h1222 h12213 h12811 h12812 h37 h38 h39 h
      hext hU hV₂ hgP hgH h5
  · exact hM22 G T L V h hext hU V₂ g hV₂ hgP hgH D h6

theorem lemma14413Big_of_inputs_F4 (h1442 : Lemma1442Big_F4) (h1449 : Lemma1449Big_F4)
    (hA5 : Lemma14410A5_F4) (hM22 : Lemma14413BigM22_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (h1352 : A6.Stmt13_5_2_F4) (h1381 : Stmt13_8_1_F4) (h1222 : Stmt12_2_2_F4)
    (h12213 : Stmt12_2_13_F4) (h12811 : Lemma12_8_11_F4) (h12811h : Lemma12_8_11_hat_F4)
    (h12812 : Lemma12_8_12_two_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    Lemma14413Big_F4 :=
  lemma14413Big_of_claim_F4 h1332 h1334 h1222 h12213 h12811 h37 h39
    (lemma1434One_of_inputs_F4 h1332 h1352 h1381)
    (y1444Claim_of_inputs_F4 h1442 h1449 hA5 hM22 h1332 h1334 h1222 h12213 h12811 h12811h h12812 h37
      h38 h39)

end CFSG.Quasithin.H13.L14413
