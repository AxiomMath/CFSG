module

public import Certificates.Certificate13604
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharStabilizer

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Steinberg

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem f4ThreeCheck_spec :
    orbitCheck3 .F4 f4ThreeReps f4ThreeOrbit = true ∧
      ∀ S ∈ [f4ThreeStab0, f4ThreeStab1, f4ThreeStab2, f4ThreeStab3],
        S.check f4Certificate = true ∧ (S.passing f4Certificate).length ≤ 1 := by
  have h := Certificates.certificate13604
  simpa only [f4ThreeCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] using h

theorem f4ThreeOrbit_check :
    orbitCheck3 .F4 f4ThreeReps f4ThreeOrbit = true := (f4ThreeCheck_spec).1

theorem card_kernelPosStabilizer_le_F4_three :
    ∀ ρ < f4ThreeReps.length,
    Nat.card (kernelPosStabilizer (triChar (τ := .F4) (vec3 (f4ThreeReps.getD ρ [])))) ≤ 1 := by
  intro ρ hρ
  have hlen : f4ThreeReps.length = 4 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · obtain ⟨hc, hp⟩ := (f4ThreeCheck_spec).2 f4ThreeStab0 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le f4Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := (f4ThreeCheck_spec).2 f4ThreeStab1 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le f4Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := (f4ThreeCheck_spec).2 f4ThreeStab2 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le f4Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := (f4ThreeCheck_spec).2 f4ThreeStab3 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le f4Certificate_check hc).trans hp

theorem charStabilizer_eq_kernelWeylGroup_F4_three
    (χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* Z3) :
    charStabilizer χ = kernelWeylGroup χ :=
  charStabilizer_eq_of_card_le_one
    (card_charQuotient_le_of_orbitCheck3 f4ThreeOrbit_check card_kernelPosStabilizer_le_F4_three χ)

theorem rootCharStabilizerSubgroup_eq_kernelReflectionGroup_F4_three
    {K : Type} [Field K]
    (a : Fin Tag.F4.rank → Kˣ) (h3 : ∀ i, a i ^ 3 = 1) :
    rootCharStabilizerSubgroup a = kernelReflectionGroup a :=
  rootCharStabilizerSubgroup_eq_kernelReflectionGroup_of_triChar
    (fun χ => (charStabilizer_eq_kernelWeylGroup_F4_three χ).le) a h3

end CFSG.HardMathSupport.Timmesfeld.Steinberg
