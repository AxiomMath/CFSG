module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC32b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC33h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk7

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

theorem lemma14_7_32_of_F4
    (h7 : Lemma14_7_7_F4) (h30 : Lemma14_7_30_F4) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h29 : Thm14_7_29_F4)
    (hSzB : SzAutBorelThree) (hD36 : D36) (hD37 : D37) (hD321 : D321) (hI5 : Insp5a)
    (hL2 : Lemma14_7_32_L2_F4) : Lemma14_7_32_F4 := by
  intro G _ _ T L V H S K hK
  by_contra hT
  obtain ⟨-, -, S₀, hF⟩ := h30 G T L V H S K hK
  have hK₀ : conjClosure K T ≠ K := fun h => hT (by
    rw [← h]
    exact le_normalizer_conjClosure K T)
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have h5 := (F918_5' hF (sqtkGroup_of_setting S₀) hK₀ hV₁I hIU W hW hirrU hD36 hD37 hD321 hI5
    hA37 hA38).1
  obtain ⟨eA⟩ := L1295B.nonempty_mulEquiv_autIH hF
  have h5' : FiveShape (cStar K) := fiveShape_congr ((cStarEquiv K).trans eA).symm h5
  rcases h5' with ⟨n, hn⟩ | ⟨n, hn⟩ | hn | hn
  · exact (hL2 G T L V H S K hK hT).1 n hn
  · exact false_of_sz_F4 h7 h30 h1222 h1332 h1334 hA37 hA38 h29 hSzB S hK hn
  · exact (hL2 G T L V H S K hK hT).2 hn
  · exact false_of_l32_F4 h30 h1222 h1332 h1334 hA37 hA38 S hK hT hn

end CFSG.Quasithin.H13.L32A.C
