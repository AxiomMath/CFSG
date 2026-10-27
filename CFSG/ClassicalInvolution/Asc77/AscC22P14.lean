module

public import CFSG.ClassicalInvolution.Asc77.AscC22P13
public import CFSG.ClassicalInvolution.Asc77.AscC22P10
import CFSG.ClassicalInvolution.Asc77.AscT8Layer

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

set_option linter.unusedSectionVars false

namespace C22P

section Named

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C22_genY : Prop :=
  p ^ f % 4 = 1 → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ K₄ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃ →
      (∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) → LayerOrthType p f Ω (u₁ * u₂) 6 (piSign p f) →
        K₄ ∈ twinSet Ω K → K₄ ≠ K → K₄ ≠ K' → K₄ ≠ K₃ →
          ∀ (R R' : Subgroup G) (b b' y : G),
            FrameData Ω K₃ K₄ z (u₁ * u₂) R R' b b' y →
              rLayer Ω (u₁ * u₂) ≤
                (conjSub y K₄ ⊔ K₃ ⊔ conjSub y K₃ ⊔ K₄) ⊔ oddCoreOf (rLayer Ω (u₁ * u₂))

end Named

section Reduction

variable {p f : ℕ} [Fact p.Prime]


theorem c22_normY_of_genY (h : C22_genY p f) : C22_normY p f := by
  intro hq1 G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ hs hW hLG
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨K₄, hK₄, h41, h42, h43, -⟩ := fourTwins_S hs hW
  have hbig : S22.Big Ω K := S22.Big.of_four hs hK₄ h41 h42 h43
  obtain ⟨R, R', b, b', y, hF, hyα⟩ := frame_at_alpha hs hK₄ h41 h42 h43 hW
  have hgen := h hq1 G Ω K K' K₃ K₄ z u₁ u₂ u₃ hs hW hLG.1 hK₄ h41 h42 h43 R R' b b' y hF
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

end Reduction

end C22P

section Final

variable {p f : ℕ} [Fact p.Prime]


theorem c22_chainPos_of_genY (h : C22P.C22_genY p f) : R31.C22_chainPos p f :=
  c22_chainPos_of_normY (C22P.c22_normY_of_genY h)

end Final

end CFSG.ClassicalInvolution.Asc77
