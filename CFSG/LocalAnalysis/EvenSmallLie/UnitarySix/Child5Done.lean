module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5Final
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2G1
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5Theta

public section

namespace CFSG.EvenSmallLie.UnitarySix.Child5

open Subgroup CFSG.ABGLocalTools CFSG.Blueprint CFSG.Fischer
open CFSG.EvenSmallLie.UnitarySix.YamadaEnd CFSG.EvenSmallLie.UnitarySix.YamadaSec3
open scoped MatrixGroups

section Inputs₄

@[expose] def K1ModelInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L : Subgroup G}, StandardSetting G L → center L = ⊥ →
    LieModel (L ⧸ center L) .PSU 6 2 1 → ∀ {t : G}, t ∈ centralizer (L : Set G) →
    orderOf t = 2 → ∀ e : L ≃* T46, ∃ χ : msigma F4 ≃* (sec3DData e t).K₁,
      (∀ A : msigma F4, (A : SL(4, F4)) ∈ pstd F4 → (χ A : G) ∈ sS e) ∧
      (χ YamadaN2.dωS : G) ∈ sK₂ e

end Inputs₄

section Coords

theorem y13CoordInput : Y13CoordInput := by
  intro G _ _ L _ _ _ t _ _ e
  exact ⟨thetaK₁ e t, ιK₁ e t, y13Coords e t⟩

end Coords

section Main

theorem n1PInput_of (hA : HypAutInput) (hcase : CaseInput) (hK : K1ModelInput) : N1PInput := by
  intro G _ _ L hset hZ hQ t htL ht e θ ιG hco P hPs hPc hPH hSP hD₁P hD₂P hV₁P htP
  have : IsSimpleGroup G := hset.simple
  obtain ⟨hH, hB, hC, hQq, h416, hcase'⟩ := sec3DInput_of hA hcase hset hZ hQ htL ht e
  have hV : ∀ v ∈ (sec3DData e t).V₁, v * v = 1 :=
    fun v hv => hH.V₁_sq hset.nonab hset.kProper hv
  have hN := hH.yamada_4_16_3 hB hC hV hQq h416 hcase'
  obtain ⟨h4a, h4b⟩ := hH.yamada_4_16_4 hB hC hV hQq h416 hcase'
  have s0 := section3Out hset hZ hQ htL ht F4 nat_card_F4 e ⊥ ⊥ ⊥ ⊥ ⊥ ⊥
  have hY13 := y13Hyp_of hH hB hC hV h416 hco s0.K₁_A₁ hN
  obtain ⟨χ, hχS, hχK⟩ := hK hset hZ hQ htL ht e
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := YamadaN2.Y13Hyp.P_facts hY13 YamadaInputs.l44Input χ hχS
    hPs hSP hD₁P hD₂P h4a h4b (hH.card_D₁_inf_D₂ hB hV).le
  exact ⟨f1, f2, f3, f4, (χ YamadaN2.dωS : G), hχK, f5, f6, f7⟩

theorem childU6Centerless_of_done (hA : HypAutInput) (hcase : CaseInput) (hY : Y13CoordInput)
    (hY₂ : Y14CoordInput) (hK : K1ModelInput) : ChildU6Centerless :=
  childU6Centerless_of_open hA hcase hY hY₂ (n1PInput_of hA hcase hK)

theorem childU6Centerless_of_done' (hA : HypAutInput) (hcase : CaseInput)
    (hY₂ : Y14CoordInput) (hK : K1ModelInput) : ChildU6Centerless :=
  childU6Centerless_of_done hA hcase y13CoordInput hY₂ hK

end Main

end CFSG.EvenSmallLie.UnitarySix.Child5
