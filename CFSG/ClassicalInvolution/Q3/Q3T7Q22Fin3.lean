module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Fin2
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Chain
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22H51z
public import CFSG.ClassicalInvolution.Q3.Q3T7ExitD4Phan
public import CFSG.ClassicalInvolution.Q3.Q3T7P25Bridge
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22M11Proof

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected


theorem c22_9Ex [Fact Q3T7E.ThmEWithSylow3] [Fact Q3T8.Asc77.Hyp22Hyp51z]
    [Fact Q3T8.Asc77.Hyp22Hyp51u] [Fact Q3T8.Asc77.ExactMembersHyp22]
    [Fact Q3T8.Asc77.C22G.PsuLayerApi3] [Fact Q3T8.Asc77.S16.M11NoInverted3] :
    Q3T8.Asc77.C22_9 := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h
  have hs := h.setting
  have hWyl := Q3T8.Asc77.S22.hyp22SettingWyl_of_ab (Q3T8.Asc77.S16.hyp22FourthTwinAb_proved)
  have hW : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W := hWyl G Ω K K' K₃ z u₁ u₂ u₃ hs
  have h4 := Q3T8.Asc77.T7V.hyp22FourTwins_of_wyl hWyl
  have hF := Q3T8.Asc77.T7V.hyp22Fuse_of_wyl hWyl
  have hL : Q3T8.Asc77.LayerOrthType Ω (u₁ * u₂) 6 (piSign 3 1) :=
    Q3T8.Asc77.c22_8X_layer_of_inputs h4 hF h
  have hG : (⨆ M ∈ twinSet Ω K, M) ⊔ rLayer Ω (u₁ * u₂) = ⊤ :=
    Q3T8.Asc77.C22G.c22_8Gen_proved G Ω K K' K₃ z u₁ u₂ u₃ h
  obtain ⟨U, hUΩ, hcomm, hpair, hgen, hH3⟩ :=
    Q3T8.Asc77.R31.c22_phanChainEx_proved (by norm_num) G Ω K K' K₃ z u₁ u₂ u₃ h hW ⟨hL, hG⟩
  have hnab : ∃ x y : G, x * y ≠ y * x := by
    obtain ⟨z', hz'⟩ := hs.stand.modU.classical K hs.stand.mem
    exact Q3T8.Asc77.exists_noncomm_of_isClassicalMember hz'
  exact Or.inl (conclusionD_of_d4PhanChain3 hnab ⟨U, hUΩ, hcomm, hpair, hgen, hH3⟩)

theorem c22_1Three_of_ex (hE : Q3T7E.ThmEWithSylow3)
    (hu51 : Q3T8.Asc77.Hyp22Hyp51u) (hEx : Q3T8.Asc77.ExactMembersHyp22) : C22_1Three := by
  have : Fact Q3T7E.ThmEWithSylow3 := ⟨hE⟩
  have : Fact Q3T8.Asc77.Hyp22Hyp51z := ⟨hyp22Hyp51z_proved⟩
  have : Fact Q3T8.Asc77.Hyp22Hyp51u := ⟨hu51⟩
  have : Fact Q3T8.Asc77.ExactMembersHyp22 := ⟨hEx⟩
  have : Fact Q3T8.Asc77.C22G.PsuLayerApi3 := ⟨psuLayerApi3_proved⟩
  have : Fact Q3T8.Asc77.S16.M11NoInverted3 := ⟨Q3T8.Asc77.S16.m11NoInverted3_proved⟩
  intro G _ _ _ Ω K K' z hs hperp
  exact Q3T8.Asc77.c22_1_of_steps Q3T8.Asc77.c22_setup c22_9Ex G Ω K K' z
    (Q3T7P25.std7_of_three hs) hperp

end CFSG.ClassicalInvolution.Q3.Q3T7
