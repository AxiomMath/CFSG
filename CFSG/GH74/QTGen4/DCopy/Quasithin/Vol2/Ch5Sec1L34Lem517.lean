module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Inputs517Odd
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Odd
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34OddF81
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34OddNat
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem522S331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem Hyp5_1_14.exists_setup5_1_17Odd_F4 {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]
    {T M L V H B D : Subgroup G} {n : ℕ} (h : Hyp5_1_14 G T M L V H B D n)
    (hI : L2OddInnerFact) (hL : L34SylowNormFact) (hF : L2TorusFact) (h515 : Stmt5_1_15_F4)
    (h516 : Stmt5_1_16_F4) (hIrr : IrrPlusBaseNonempty) (h323 : Stmt3_2_3) (h325 : Stmt3_2_5_F4)
    (h3228 : Stmt3_2_2_eight) (h513 : Stmt5_1_3_F4) (h5114 : Stmt5_1_14_first_F4) (hn : Odd n) :
    ∃ V₀ : Subgroup G, Setup5_1_17Odd G T M L V₀ H B D n := by
  obtain ⟨V₀, hmod, hnat, hV₀T, hTV₀, hTIM⟩ :=
    h.exists_natural_of_odd_F4 hIrr h323 h325 h3228 h513 h5114 hn
  have hDC := h.D_le_centralizerModO2_of_odd_F4 hI hL hF h515 hn
  have hDM := h.D_le_normalizer_K_of_odd_F4 h515 hn
  obtain ⟨h3, hsol⟩ := h516 G T M L V₀ H B D n h.hyp h.notation59 hmod h.l34
  have hsolv : Group.IsSolvable ↥(centralizerModO2 (oTwoUpper H)) := by
    by_contra hns
    exact (hsol hns).2.2 hDM
  exact ⟨V₀, ⟨h.hyp, h.notation59, hmod, h.l34⟩, hn, hnat, hV₀T, hTV₀, hTIM, hDC, hDM, hsolv, h3⟩

theorem stmt5_1_17_F81_of_F4
    (h5114 : Stmt5_1_14_first_F4) (hI : L2OddInnerFact) (hF : L2TorusFact) (h323 : Stmt3_2_3)
    (h510 : Stmt5_1_10_F4) (hBor : L34BorelFact) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D : Subgroup G) (n : ℕ),
      Setup5_1_17Odd G T M L V H B D n →
      IsTISetUnder (quasithinOmegaOneCenter T ⊓ V) ⊤ →
      (∀ H₁ : Subgroup G, H ⊔ D ≤ H₁ →
          H₁ ≤ Subgroup.normalizer ((quasithinOmegaOneCenter T ⊓ V : Subgroup G) : Set G) →
          IsElemAbelian 2 (conjClosure V H₁)) →
        HypF81 T V L (quasithinOmegaOneCenter T ⊓ V) (H ⊔ D) := by
  intro G _ _ T M L V H B D n s hTI habel
  exact s.hypF81_F4 h5114 hI hF h323 (s.hyp.card_B_dvd_three_F4 h510 hBor) hTI habel

theorem stmt5_1_17_of_inputs_F4
    (hI : L2OddInnerFact) (hL : L34SylowNormFact) (hF : L2TorusFact)
    (h515 : Stmt5_1_15_F4) (h516 : Stmt5_1_16_F4) (hIrr : IrrPlusBaseNonempty) (h323 : Stmt3_2_3)
    (h325 : Stmt3_2_5_F4) (h3228 : Stmt3_2_2_eight) (h513 : Stmt5_1_3_F4) (h5114 : Stmt5_1_14_first_F4)
    (h510 : Stmt5_1_10_F4) (hBor : L34BorelFact)
    (hTI : Stmt5_1_17_TI_F4) (hab : Stmt5_1_17_abelian_F4) (ham : Stmt5_1_17_amalgam) :
    Stmt5_1_17_F4 := by
  have hF81 := stmt5_1_17_F81_of_F4 h5114 hI hF h323 h510 hBor
  intro G _ _ T M L V H B D n hyp hN hV hK
  by_contra hne
  have hn : Odd n := Nat.not_even_iff_odd.mp hne
  obtain ⟨V₀, hs⟩ := (⟨hyp, hN, hV, hK⟩ : Hyp5_1_14 G T M L V H B D n).exists_setup5_1_17Odd_F4
    hI hL hF h515 h516 hIrr h323 h325 h3228 h513 h5114 hn
  have hTIG := hTI G T M L V₀ H B D n hs
  exact ham G T M L V₀ H B D n hs hTIG
    (hF81 G T M L V₀ H B D n hs hTIG (hab G T M L V₀ H B D n hs hTIG))

end CFSG.Quasithin.H13
