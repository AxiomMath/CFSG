module

public import CFSG.ClassicalInvolution.Asc77.AscC22P17
import CFSG.ClassicalInvolution.Asc77.AscS16P
import CFSG.ClassicalInvolution.Asc77.AscT8Layer

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected

namespace C22P

set_option linter.unusedSectionVars false

section Norm

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}


theorem normY_of_hyp22Setting (hq1 : p ^ f % 4 = 1)
    (hs : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) :
    rLayer Ω (u₁ * u₂) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hW : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W :=
    S22.hyp22SettingWyl_of_ab (S16.hyp22FourthTwinAb_proved p f) G Ω K K' K₃ z u₁ u₂ u₃ hs
  obtain ⟨K₄, hK₄, h41, h42, h43, -⟩ := fourTwins_S hs hW
  have hbig : S22.Big Ω K := S22.Big.of_four hs hK₄ h41 h42 h43
  obtain ⟨R, R', b, b', y, hF, hyα⟩ := frame_at_alpha hs hK₄ h41 h42 h43 hW
  have hgen := c22_gen_frame hq1 hs hW hK₄ h41 h42 h43 hF
  have h2 := S22.c22_2S p f
  set α₀ := alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) with hα₀
  have hK₃N : K₃ ≤ Subgroup.normalizer (α₀ : Set G) :=
    S22.twin_le_normalizer_alpha h2 hs hbig hs.hK₃
  have hK₄N : K₄ ≤ Subgroup.normalizer (α₀ : Set G) :=
    S22.twin_le_normalizer_alpha h2 hs hbig hK₄
  have hconjN : ∀ {M : Subgroup G}, M ≤ Subgroup.normalizer (α₀ : Set G) →
      conjSub y M ≤ Subgroup.normalizer (α₀ : Set G) := by
    intro M hM x hx
    rw [mem_conjSub_iff] at hx
    have e : x = y * (y⁻¹ * x * y) * y⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyα (hM hx)) (Subgroup.inv_mem _ hyα)
  have hu2 : (u₁ * u₂) * (u₁ * u₂) = 1 := hs.sq_12
  have hrL : rLayer Ω (u₁ * u₂) = exactLayer Ω (u₁ * u₂) := rLayer_eq_exactLayer hp hq hΩ hu2
  have hOle : oddCoreOf (rLayer Ω (u₁ * u₂)) ≤
      oddCoreOf (Subgroup.centralizer ({u₁ * u₂} : Set G)) := by
    rw [hrL]
    refine T8.oddCoreOf_le_oddCoreOf_of_normalized (exactLayer_le_centralizer Ω (u₁ * u₂))
      (fun c hc => ?_)
    have hcu : c * (u₁ * u₂) * c⁻¹ = u₁ * u₂ := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hc
      calc c * (u₁ * u₂) * c⁻¹ = ((u₁ * u₂) * c) * c⁻¹ := by rw [← this]
        _ = u₁ * u₂ := by group
    rw [← exactLayer_conj hΩ.conjInvariant c (u₁ * u₂), hcu]
  have hO : oddCoreOf (rLayer Ω (u₁ * u₂)) ≤ Subgroup.normalizer (α₀ : Set G) :=
    hOle.trans (oddCore_centralizer_le_normalizer_alpha hs hbig)
  exact hgen.trans (sup_le (sup_le (sup_le (sup_le (hconjN hK₄N) hK₃N) (hconjN hK₃N)) hK₄N) hO)

theorem normY_of_hyp22 (hq1 : p ^ f % 4 = 1) (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) :
    rLayer Ω (u₁ * u₂) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) :=
  normY_of_hyp22Setting hq1 h.setting

end Norm

end C22P

end CFSG.ClassicalInvolution.Asc77
