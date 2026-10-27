module

public import CFSG.Quasithin.Vol2.Ch5Assembly
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL3S
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113D4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec3Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Statements
import CFSG.Quasithin.Vol2.Ch5Sec1Hall
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsC
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem stmt5_2_3S_of_inputs_F4 (h515 : Stmt5_1_5_F4) (h5114 : Stmt5_1_14_F4) (h522 : Stmt5_2_2C_F4)
    (h529 : Stmt5_2_9_F4) (h5210 : Stmt5_2_10_F4) (hLie : Stmt5_3_Lie_F4) (hL2 : Ch5L2ChoiceExists_F4)
    (hL34c : Ch5L34Conclusion) (hKZ : Ch5KZConclusion) (hKZ3 : Ch5KZConclusionD4) :
    Stmt5_2_3S_F4 := by
  intro G _ _ T M L H V m hsimple hnab hqtke hT hM hTM hLmax hLf hLM hMN h2m hlie hH hq hV
    hVred hVL
  have h501 : Hyp5_0_1 G T M L m :=
    ⟨hsimple, hnab, hqtke, hT, hM, hTM, hLmax, hLf, hLM, hMN, h2m, hlie⟩
  have h518 : Hyp5_1_8 G T M L H m := ⟨h501, hH, hq⟩
  have hmod : IsCh5Module T L V := ⟨hV, hVred, hVL⟩

  obtain ⟨D, hD⟩ := h501.exists_isHall_borel
  obtain ⟨-, -, hB⟩ := h515 G T M L H D m h501 hH hD
  obtain ⟨-, B, hB, hBD⟩ := hB hq
  have h519 : IsNotation5_1_9 T M L H B D := ⟨by rwa [inf_comm], hD, hBD⟩
  by_cases hL34 : LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2
  ·
    have hc := h5114 G T M L V H B D m h518 h519 hmod hL34
    exact Or.inl ⟨hc.2.2.2.1.1, hL34c G T M L V H B D m h518 h519 hmod hL34 hc⟩
  by_cases hDK : D ≤ Subgroup.normalizer (oTwoUpper H : Set G)
  ·
    obtain ⟨L₂, hL₂⟩ := hL2 G T M L H B D m h518 h519
    have h524 : Hyp5_2_4 G T M L V H B D L₂ m :=
      { toHyp5_1_8 := h518, notation59 := h519, ch5Module := hmod, notL34 := hL34, D_le := hDK,
        choice := hL₂ }
    rcases h529 G T M L V H B D L₂ m h524 with ⟨f, hf, h1⟩ | ⟨k, rfl, hk, h2⟩ | h3 | h4
    · refine Or.inr (Or.inr (Or.inl ?_))
      rcases h1 with h1 | h1 | h1 | h1 | h1
      · exact ⟨.PSL, 3, f, hf, Or.inl ⟨rfl, rfl⟩, admissible_PSL3 hf,
          hLie G T M L V H B D L₂ _ _ _ _ h524 h1 ⟨hf, Or.inl ⟨rfl, rfl⟩⟩⟩
      · exact ⟨.PSp, 2, f, hf, Or.inr (Or.inl ⟨rfl, rfl⟩), admissible_PSp2 hf,
          hLie G T M L V H B D L₂ _ _ _ _ h524 h1 ⟨hf, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩⟩
      · exact ⟨.G2, 0, f, hf, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))), admissible_G2 hf,
          hLie G T M L V H B D L₂ _ _ _ _ h524 h1 ⟨hf, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩⟩
      · exact ⟨.trialityD4, 0, f, hf, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))),
          admissible_D4 hf, hLie G T M L V H B D L₂ _ _ _ _ h524 h1
            ⟨hf, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩⟩
      · have hG := hLie G T M L V H B D L₂ _ _ _ _ h524 h1
          ⟨hf, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
        exact ⟨.twistedF4, 0, f, hf, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))),
          admissible_of_lieModel_twistedF4 hG, hG⟩
    · have hk2 : 2 ≤ k := by omega
      exact Or.inr (Or.inr (Or.inl ⟨.PSU, 4, k, hk2, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)),
        admissible_PSU4 hk2, hLie G T M L V H B D L₂ _ _ _ _ h524 h2
          ⟨hk2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))⟩⟩))
    · exact Or.inr (Or.inr (Or.inr (hLie G T M L V H B D L₂ _ _ _ _ h524 h3
        ⟨le_rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))))⟩)))
    · exact Or.inr (Or.inl (h5210 G T M L V H B D L₂ m h524 h4))
  ·
    rcases h522 G T M L V H B D m h518 h519 hmod with h | ⟨hK, rfl, hV5, hKZ', hZ⟩ | h3
    · exact absurd h hDK
    · exact Or.inl ⟨rfl, hKZ G T M L V H 2 h518 hmod hK rfl hV5 hKZ' hZ⟩
    · exact Or.inl ⟨h3.2.1, hKZ3 G T M L V H m h518 hmod h3⟩

end CFSG.Quasithin.H13
