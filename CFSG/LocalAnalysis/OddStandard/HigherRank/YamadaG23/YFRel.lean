module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FactsS

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

structure SRel (fr : SFrame Γ) : Prop where
  z_sq : fr.z ^ 2 = 1
  h0_sq : fr.h₀ ^ 2 = 1
  a1_sq : fr.a₁ ^ 2 = fr.z
  a2_sq : fr.a₂ ^ 2 = fr.z
  b2_sq : fr.b₂ ^ 2 = fr.z
  comm1 : ⁅fr.a₁, fr.b₁⁆ = fr.z
  comm2 : ⁅fr.a₂, fr.b₂⁆ = fr.z
  a1h : ⁅fr.a₁, fr.h₀⁆ = fr.b₁ * fr.z
  a2h : ⁅fr.a₂, fr.h₀⁆ = fr.b₂ * fr.z
  b1h : ⁅fr.b₁, fr.h₀⁆ = fr.z
  b2h : ⁅fr.b₂, fr.h₀⁆ = fr.z
  a1a2 : ⁅fr.a₁, fr.a₂⁆ = 1
  a1b2 : ⁅fr.a₁, fr.b₂⁆ = 1
  b1a2 : ⁅fr.b₁, fr.a₂⁆ = 1
  b1b2 : ⁅fr.b₁, fr.b₂⁆ = 1

private abbrev w0 : FreeGroup (Fin 6) := FreeGroup.of 0
private abbrev w1 : FreeGroup (Fin 6) := FreeGroup.of 1
private abbrev w2 : FreeGroup (Fin 6) := FreeGroup.of 2
private abbrev w3 : FreeGroup (Fin 6) := FreeGroup.of 3
private abbrev w4 : FreeGroup (Fin 6) := FreeGroup.of 4
private abbrev w5 : FreeGroup (Fin 6) := FreeGroup.of 5

private lemma gens11_zero (fr : Frame Γ) : fr.gens11 0 = fr.a₁ := rfl
private lemma gens11_one (fr : Frame Γ) : fr.gens11 1 = fr.b₁ := rfl
private lemma gens11_two (fr : Frame Γ) : fr.gens11 2 = fr.a₂ := rfl
private lemma gens11_three (fr : Frame Γ) : fr.gens11 3 = fr.b₂ := rfl
private lemma gens11_four (fr : Frame Γ) : fr.gens11 4 = fr.h₀ := rfl
private lemma gens11_five (fr : Frame Γ) : fr.gens11 5 = fr.σ := rfl

theorem srel_of_fact11 [Finite Γ] (fr : Frame Γ) {L : Subgroup Γ} (h : fr.Fact11 L) :
    SRel fr.toSFrame := by
  obtain ⟨hrel, -⟩ := h.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hr := hrel ((w1 ^ 2) ^ 2) (by rw [Frame.rels11]; decide)
    simpa [SFrame.z, gens11_one] using hr
  · have hr := hrel (w4 ^ 2) (by rw [Frame.rels11]; decide)
    simpa [gens11_four] using hr
  · rw [← mul_inv_eq_one]
    have hr := hrel (w0 ^ 2 * (w1 ^ 2)⁻¹) (by rw [Frame.rels11]; decide)
    simpa [SFrame.z, gens11_zero, gens11_one] using hr
  · rw [← mul_inv_eq_one]
    have hr := hrel (w2 ^ 2 * (w1 ^ 2)⁻¹) (by rw [Frame.rels11]; decide)
    simpa [SFrame.z, gens11_two, gens11_one] using hr
  · rw [← mul_inv_eq_one]
    have hr := hrel (w3 ^ 2 * (w1 ^ 2)⁻¹) (by rw [Frame.rels11]; decide)
    simpa [SFrame.z, gens11_three, gens11_one] using hr
  · rw [← mul_inv_eq_one]
    have hr := hrel (⁅w0, w1⁆ * (w1 ^ 2)⁻¹) (by rw [Frame.rels11]; decide)
    simpa [SFrame.z, gens11_zero, gens11_one, commutatorElement_def] using hr
  · rw [← mul_inv_eq_one]
    have hr := hrel (⁅w2, w3⁆ * (w1 ^ 2)⁻¹) (by rw [Frame.rels11]; decide)
    simpa [SFrame.z, gens11_one, gens11_two, gens11_three, commutatorElement_def] using hr
  · rw [← mul_inv_eq_one]
    have hr := hrel (⁅w0, w4⁆ * (w1 * w1 ^ 2)⁻¹) (by rw [Frame.rels11]; decide)
    simpa [SFrame.z, gens11_zero, gens11_one, gens11_four, commutatorElement_def] using hr
  · rw [← mul_inv_eq_one]
    have hr := hrel (⁅w2, w4⁆ * (w3 * w1 ^ 2)⁻¹) (by rw [Frame.rels11]; decide)
    simpa [SFrame.z, gens11_one, gens11_two, gens11_three, gens11_four,
      commutatorElement_def] using hr
  · rw [← mul_inv_eq_one]
    have hr := hrel (⁅w1, w4⁆ * (w1 ^ 2)⁻¹) (by rw [Frame.rels11]; decide)
    simpa [SFrame.z, gens11_one, gens11_four, commutatorElement_def] using hr
  · rw [← mul_inv_eq_one]
    have hr := hrel (⁅w3, w4⁆ * (w1 ^ 2)⁻¹) (by rw [Frame.rels11]; decide)
    simpa [SFrame.z, gens11_one, gens11_three, gens11_four, commutatorElement_def] using hr
  · have hr := hrel (⁅w0, w2⁆) (by rw [Frame.rels11]; decide)
    simpa [gens11_zero, gens11_two, commutatorElement_def] using hr
  · have hr := hrel (⁅w0, w3⁆) (by rw [Frame.rels11]; decide)
    simpa [gens11_zero, gens11_three, commutatorElement_def] using hr
  · have hr := hrel (⁅w1, w2⁆) (by rw [Frame.rels11]; decide)
    simpa [gens11_one, gens11_two, commutatorElement_def] using hr
  · have hr := hrel (⁅w1, w3⁆) (by rw [Frame.rels11]; decide)
    simpa [gens11_one, gens11_three, commutatorElement_def] using hr

theorem frame_sigma_conj [Finite Γ] (fr : Frame Γ) {L : Subgroup Γ} (h : fr.Fact11 L) :
    fr.σ * fr.a₁ * fr.σ⁻¹ = fr.a₂ ∧ fr.σ * fr.b₁ * fr.σ⁻¹ = fr.b₂ := by
  obtain ⟨hrel, -⟩ := h.1
  have hS := srel_of_fact11 fr h
  have hz : fr.z ^ 2 = 1 := hS.z_sq
  have key : ∀ c d : Γ, d ^ 2 = fr.z → c * fr.σ * c⁻¹ * fr.σ⁻¹ = c * d * fr.z →
      fr.σ * c * fr.σ⁻¹ = d := by
    intro c d hd hcd
    have hd4 : d ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hd, hz]
    have hdz : (d * fr.z)⁻¹ = d := by
      rw [inv_eq_iff_mul_eq_one, ← hd]
      calc (d * d ^ 2) * d = d ^ 4 := by group
        _ = 1 := hd4
    have h1 : fr.σ * c⁻¹ * fr.σ⁻¹ = d * fr.z := by
      have h2 : c * (fr.σ * c⁻¹ * fr.σ⁻¹) = c * (d * fr.z) := by
        calc c * (fr.σ * c⁻¹ * fr.σ⁻¹) = c * fr.σ * c⁻¹ * fr.σ⁻¹ := by group
          _ = c * d * fr.z := hcd
          _ = c * (d * fr.z) := by group
      exact mul_left_cancel h2
    calc fr.σ * c * fr.σ⁻¹ = (fr.σ * c⁻¹ * fr.σ⁻¹)⁻¹ := by group
      _ = (d * fr.z)⁻¹ := by rw [h1]
      _ = d := hdz
  have hA : fr.a₁ * fr.σ * fr.a₁⁻¹ * fr.σ⁻¹ = fr.a₁ * fr.a₂ * fr.z := by
    have hr := hrel (⁅w0, w5⁆ * (w0 * w2 * w1 ^ 2)⁻¹)
      (by rw [Frame.rels11]; decide)
    have hr' : fr.a₁ * fr.σ * fr.a₁⁻¹ * fr.σ⁻¹ * (fr.a₁ * fr.a₂ * fr.z)⁻¹ = 1 := by
      simpa [SFrame.z, gens11_zero, gens11_one, gens11_two, gens11_five,
        commutatorElement_def] using hr
    exact mul_inv_eq_one.mp hr'
  have hB : fr.b₁ * fr.σ * fr.b₁⁻¹ * fr.σ⁻¹ = fr.b₁ * fr.b₂ * fr.z := by
    have hr := hrel (⁅w1, w5⁆ * (w1 * w3 * w1 ^ 2)⁻¹)
      (by rw [Frame.rels11]; decide)
    have hr' : fr.b₁ * fr.σ * fr.b₁⁻¹ * fr.σ⁻¹ * (fr.b₁ * fr.b₂ * fr.z)⁻¹ = 1 := by
      simpa [SFrame.z, gens11_one, gens11_three, gens11_five, commutatorElement_def] using hr
    exact mul_inv_eq_one.mp hr'
  exact ⟨key fr.a₁ fr.a₂ hS.a2_sq hA, key fr.b₁ fr.b₂ hS.b2_sq hB⟩

end CFSG.OddStandard.HigherRank.YamadaG23
