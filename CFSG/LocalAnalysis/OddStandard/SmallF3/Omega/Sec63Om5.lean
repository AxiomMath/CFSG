module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63Norm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79Model
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Chain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec63_no_om5_om6p [Finite G] (hP : Asc82Tab6P) (hHyp : Asc82Hyp62 G) {Z Y : Subgroup G}
    (h : WalterArrow Z Y) (hZ : IsOmega5 Z) (hY : IsOmega6Plus Y) : False := by
  obtain ⟨x, y, hx, hy, -, hZc, hYc, hZY, hcomm⟩ := h
  have hL : IsOm6P Y := ⟨hYc.isQuasisimple, hY⟩
  have hH : Hyp62At Y := hHyp Y ⟨y, hy, hYc⟩ hY
  have hxN : x ∈ normalizer (Y : Set G) := sec63_mem_normalizer_of_comm hcomm
  have hZin : IsComponentIn Z (Y ⊓ centralizer ({x} : Set G)) :=
    hZc.mono (le_inf hZY hZc.le) inf_le_right
  have hZle : Z ≤ layerCent Y x := hZin.le_layerCent
  have h25920 : ctrQ Z = 25920 := ctrQ_of_psp4 hZc.isQuasisimple hZ
  have hbot : layerCent Y x ≠ ⊥ := fun hb => hZc.ne_bot (le_bot_iff.mp (hb ▸ hZle))
  have hnot : ctrQ (layerCent Y x) = 360 ∨ ctrQ (layerCent Y x) = 5616 ∨
      ctrQ (layerCent Y x) = 6048 → False := by
    intro hd
    have hdvd := ctrQ_dvd_of_le hZle
    rw [h25920] at hdvd
    rcases hd with hd | hd | hd <;> rw [hd] at hdvd <;> omega
  rcases hP.classify G Y hL x hx hxN with hc | h4 | h2 | h1 | h3 | hout
  · have hYx : Y ≤ centralizer ({x} : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hc a ha)
    have hbot' := commutator_zpowers_eq_bot_of_le_centralizer hYx
    rw [hcomm] at hbot'
    exact hYc.ne_bot hbot'
  · exact hbot ((hP.layer_trivial G Y hL x hx hxN).mpr (Or.inl h4))
  · have h29 : IsL29 (layerCent Y x) := hP.layer_i2 G Y hL x hx hxN h2
    exact hnot (Or.inl (ctrQ_of_l29
      (isComponentIn_layerCent (Or.inr (Or.inl h29))).isQuasisimple h29))
  · exact sec79_hyp62_no_i1 hP hL hH hx hxN h1
  · exact hbot ((hP.layer_trivial G Y hL x hx hxN).mpr (Or.inr h3))
  · rcases hP.layer_outer G Y hL x hx hxN hout with h3 | h29
    · have hq := (isComponentIn_layerCent (Or.inr (Or.inr (Or.inr h3)))).isQuasisimple
      rcases h3 with h3 | h3
      · exact hnot (Or.inr (Or.inl (ctrQ_of_l33 hq h3)))
      · exact hnot (Or.inr (Or.inr (ctrQ_of_u33 hq h3)))
    · exact hnot (Or.inl (ctrQ_of_l29
        (isComponentIn_layerCent (Or.inr (Or.inl h29))).isQuasisimple h29))

end CFSG.OddStandard.SmallF3.Omega
