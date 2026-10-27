module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf9Layer

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Tri

@[expose] def LayerTri {Y : Type} [Group Y] [Finite Y] (Ω : Set (Subgroup Y)) (K₃ K₄ : Subgroup Y)
    (u : Y) : Prop :=
  LayerDataR Ω K₃ K₄ u ∨ ¬ SecNoExitAt Ω u

@[expose] def V3Tri (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y), V3Std n Y R S t K K' K₃ u₁ u₂ u₃ →
      ∀ K₄ : Subgroup Y,
        FourthTwin (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ K₄ →
          LayerTri (CoreAssembly.conjClass (tightCore R)) K₃ K₄ (u₁ * u₂)

variable {n : ℕ}

theorem v3LayerDataR_of_noExit (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (h4 : Thm4RTwinBelow 3 n) {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R}
    {t : Y} {K K' K₃ K₄ : Subgroup Y} {u₁ u₂ u₃ : Y}
    (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    (hF : FourthTwin (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ K₄)
    (hno : SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) :
    LayerDataR (CoreAssembly.conjClass (tightCore R)) K₃ K₄ (u₁ * u₂) := by
  obtain ⟨hne_top, hP3, hP4⟩ := v3_layerBasics hStd hF
  refine ⟨hne_top, hP3, hP4, fun R₃ R₄ h3 h4' c3 c4 => ?_⟩
  have hd := hStd.datum
  obtain ⟨hmem, -⟩ := v3_tq_members hStd hF
  have hne : (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)).Nonempty :=
    ⟨_, secImg_mem_secFam hmem⟩
  obtain ⟨h2', hl, hex, hLie⟩ :=
    layer_lieDecomp hcit hP hStd.perp hd.sq_12 hd.mul_ne_one hne hno
  exact v3LayerGen_of_trans (v3LayerTrans_of_thm4 h4) Y _ S t K K' K₃ u₁ u₂ u₃ hStd K₄ hF hno h2' hl
    hex hLie R₃ R₄ h3 h4' c3 c4

theorem v3Tri_of_thm4 (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (h4 : Thm4RTwinBelow 3 n) : V3Tri n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ hStd K₄ hF
  by_cases hno : SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)
  · exact Or.inl (v3LayerDataR_of_noExit hcit hP h4 hStd hF hno)
  · exact Or.inr hno

@[expose] def V3Alpha13 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y), V3Std n Y R S t K K' K₃ u₁ u₂ u₃ →
      ∀ (K₄ : Subgroup Y),
        FourthTwin (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ K₄ →
          LayerTri (CoreAssembly.conjClass (tightCore R)) K₃ K₄ (u₁ * u₂) →
            alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) = ⊥

end Tri

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
