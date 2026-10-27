module

public import CFSG.ClassicalInvolution.Asc77.AscC25V39
public import CFSG.ClassicalInvolution.Asc77.AscC25V41

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

section Main

variable {p f : ℕ} [Fact p.Prime]


variable (p f) in
@[expose] def EvenResiduals : Prop :=
  (f % 4 = 2 → DIAG25 p f) ∧ (f % 4 = 0 → G1Omega6 p f ∧ DIAGS25 p f)

theorem g1Nine_of_ne (h : p ^ f ≠ 9) : G1Nine p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ t' _ h9
  exact absurd h9 h

theorem res25_of_pm (h11 : C25_11 p f) (hf4 : f % 4 = 2) (hD : DIAG25 p f) : RES25 p f :=
  res25_of_parts (gcs25z_of_pm h11 hf4) hD

theorem res25_of_four_dvd (hf0 : f % 4 = 0) (hG6 : G1Omega6 p f) (hD : DIAGS25 p f) :
    RES25 p f := by
  refine res25_of_g1 (g1_25_of_omega6 hG6) (g1Nine_of_ne ?_) hD
  intro h9
  rcases Nat.eq_zero_or_pos f with h0 | h0
  · rw [h0, pow_zero] at h9
    omega
  · have hf4 : 4 ≤ f := by omega
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have h1 : 2 ^ 4 ≤ p ^ f := calc
      2 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left hp2 4
      _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf4
    omega

theorem res25_of_even (h11 : C25_11 p f) (hf : Even f) (h2 : f % 4 = 2 → DIAG25 p f)
    (h0 : f % 4 = 0 → G1Omega6 p f ∧ DIAGS25 p f) : RES25 p f := by
  have hf2 : f % 2 = 0 := Nat.even_iff.mp hf
  by_cases hf4 : f % 4 = 2
  · exact res25_of_pm h11 hf4 (h2 hf4)
  · have hf0 : f % 4 = 0 := by omega
    exact res25_of_four_dvd hf0 (h0 hf0).1 (h0 hf0).2

theorem c25_16invEven_of_residuals (h11 : C25_11 p f) (hmix : Mix25 p f)
    (h2 : f % 4 = 2 → DIAG25 p f) (h0 : f % 4 = 0 → G1Omega6 p f ∧ DIAGS25 p f) :
    Even f → T7U.C25_16inv p f :=
  fun hf => c25_16inv_of_res h11 hmix (res25_of_even h11 hf h2 h0)

theorem c25_16invEven_of_evenResiduals (h11 : C25_11 p f) (hmix : Mix25 p f)
    (hres : EvenResiduals p f) : Even f → T7U.C25_16inv p f :=
  c25_16invEven_of_residuals h11 hmix hres.1 hres.2

end Main

end CFSG.ClassicalInvolution.Asc77.C25V
