module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113D4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Final
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native38
public import CFSG.Quasithin.Background.KnownMultTypes
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Lie

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

theorem stmt5_1_13_lieC_of_F4
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hF : FactF5113)
    (hD42 : Stmt5_1_13_lie_D42C_F4) : Stmt5_1_13_lieC_F4 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n k hyp hN hk hV hK₁ hKeq hX hhat hlt htype
  by_cases hres : ∃ U P : Subgroup (O2Q (conjClosure Kh₁ T)), IsSylowTwoOf U ⊤ ∧ U ≤ P ∧
      P ⋖ ⊤ ∧ Group.IsSolvable ↥P
  · exact hD42 G T M L V H B D K₁ X Kh₁ n k hyp hN hk hV hK₁ hKeq hX hhat hlt htype hres
  · have e : Emb512 G T M L H B D K₁ X Kh₁ n k := ⟨hyp, hN, hk, hK₁, hKeq, hX, hhat, hlt⟩
    exact Or.inl (e.lie_normalizes h37 h38 hF htype hres)

theorem stmt5_1_13_lieC_of_inputs_F4
    (hF : FactF5113) (hD42 : Stmt5_1_13_lie_D42C_F4) : Stmt5_1_13_lieC_F4 :=
  stmt5_1_13_lieC_of_F4 Vol2Native.a37ForSQTKCat_proved
    (Vol2Native.a38ForSQTKCat_of_facts CFSG.Quasithin.mult2Fact Vol2Native.a134SQTKFactCat
      Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved) hF hD42

theorem stmt5_1_13C_of_F4
    (h38 : Vol2Native.A38ForSQTKCat) (h510 : Stmt5_1_10_F4) (h5112 : Stmt5_1_12_F4)
    (hlie : Stmt5_1_13_lieC_F4) (hmain : Stmt5_1_13_main_F4) : Stmt5_1_13C_F4 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n hyp hN hV hK₁ hKeq hX hhat
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  obtain ⟨k, hk⟩ := h510.exists_fieldParam_F4 hyp hN
  by_cases hDK : D ⊓ X ≤ Subgroup.normalizer (oTwoUpper H : Set G)
  · exact Or.inl hDK
  right

  have hSX : IsSylowTwoOf T X := h.isSylowTwoOf (hyp.hStar.1.1.trans hX.1)
  have hXN : X ≤ Subgroup.normalizer (conjClosure Kh₁ T : Set G) :=
    Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hloc Vol2Native.a37ForSQTKCat_proved h38
      hX.2 hSX hhat.1

  obtain ⟨Kh₁', hhat', hKle, hcases⟩ := h5112 G T M L H B D K₁ n k hyp hN hk hK₁ hKeq X hX
  have hKh : Kh₁ = Kh₁' := hhat'.2.2 Kh₁ hhat.1 hhat.2.1
  subst hKh
  rcases hcases with h1 | h2 | h3 | h4 | h5
  · exact absurd ((inf_le_right.trans hXN).trans (by rw [← h1])) hDK
  all_goals have hlt : oTwoUpper H < conjClosure Kh₁ T := lt_of_le_of_ne hKle (fun heq => hDK
    ((inf_le_right.trans hXN).trans (by rw [← heq])))
  · exact Or.inl (hmain G T M L V H B D K₁ X Kh₁ n hyp hN hV hK₁ hKeq hX hhat hlt hDK (Or.inl h2))
  · exact Or.inr ((hlie G T M L V H B D K₁ X Kh₁ n k hyp hN hk hV hK₁ hKeq hX hhat hlt
      (Or.inl h3)).resolve_left hDK)
  · exact Or.inr ((hlie G T M L V H B D K₁ X Kh₁ n k hyp hN hk hV hK₁ hKeq hX hhat hlt
      (Or.inr h4)).resolve_left hDK)
  · exact Or.inl (hmain G T M L V H B D K₁ X Kh₁ n hyp hN hV hK₁ hKeq hX hhat hlt hDK (Or.inr h5))

end CFSG.Quasithin.H13
