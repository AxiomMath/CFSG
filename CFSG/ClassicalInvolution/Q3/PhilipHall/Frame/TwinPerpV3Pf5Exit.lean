module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf5Gen
public import CFSG.ClassicalInvolution.SmallCases.A7T22Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section Exit

variable {n : ℕ}

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ K₄ : Subgroup Y} {u₁ u₂ u₃ : Y}

theorem v3_layerBasics (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    (hF : FourthTwin (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ K₄) :
    rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ≠ ⊤ ∧
      (∃ R₃ : Subgroup Y, IsSylow2In R₃ K₃ ∧ R₃ ≤ Subgroup.centralizer ({u₁ * u₂} : Set Y)) ∧
      (∃ R₄ : Subgroup Y, IsSylow2In R₄ K₄ ∧ R₄ ≤ Subgroup.centralizer ({u₁ * u₂} : Set Y)) := by
  have hd := hStd.datum
  have hC := CoreData.of_S hStd.perp.core
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.sq_12
  obtain ⟨hmem, hmem4⟩ := v3_tq_members hStd hF
  have hne_top : rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ≠ ⊤ := by
    intro htop
    have hle : rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ≤
        Subgroup.centralizer ({u₁ * u₂} : Set Y) :=
      iSup₂_le fun R' _ => iSup_le fun hR => hR
    rw [htop] at hle
    have hZ : Subgroup.center Y = ⊥ :=
      InductionBridge.center_eq_bot_of_fstar_simple hC.simple hC.nonab
    have : u₁ * u₂ ∈ Subgroup.center Y := Subgroup.mem_center_iff.mpr fun g => by
      have : g ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) := hle (Subgroup.mem_top g)
      exact Subgroup.mem_centralizer_singleton_iff.mp this
    rw [hZ] at this
    exact hd.mul_ne_one (Subgroup.mem_bot.mp this)
  obtain ⟨P₃, hP₃, hP₃c⟩ := TwinADescent.exists_sylow_centralizer_of_tq hc2 hmem.2
  obtain ⟨P₄, hP₄, hP₄c⟩ := TwinADescent.exists_sylow_centralizer_of_tq hc2 hmem4.2
  exact ⟨hne_top, ⟨P₃, hP₃, hP₃c⟩, ⟨P₄, hP₄, hP₄c⟩⟩

end Exit

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
