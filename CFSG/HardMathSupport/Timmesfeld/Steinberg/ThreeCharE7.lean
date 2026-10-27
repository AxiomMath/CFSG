module

public import Certificates.Certificate13605
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharStabilizer

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Steinberg

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem e7ThreeCheck_spec :
    orbitCheck3 .E7 e7ThreeReps e7ThreeOrbit = true ∧
      ∀ S ∈ [e7ThreeStab0, e7ThreeStab1, e7ThreeStab2, e7ThreeStab3, e7ThreeStab4, e7ThreeStab5],
        S.check e7Certificate = true ∧ (S.passing e7Certificate).length ≤ 1 := by
  have h := Certificates.certificate13605
  simpa only [e7ThreeCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] using h

theorem e7ThreeOrbit_check :
    orbitCheck3 .E7 e7ThreeReps e7ThreeOrbit = true := (e7ThreeCheck_spec).1

theorem card_kernelPosStabilizer_le_E7_three :
    ∀ ρ < e7ThreeReps.length,
    Nat.card (kernelPosStabilizer (triChar (τ := .E7) (vec3 (e7ThreeReps.getD ρ [])))) ≤ 1 := by
  intro ρ hρ
  have hlen : e7ThreeReps.length = 6 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · obtain ⟨hc, hp⟩ := (e7ThreeCheck_spec).2 e7ThreeStab0 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le e7Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := (e7ThreeCheck_spec).2 e7ThreeStab1 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le e7Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := (e7ThreeCheck_spec).2 e7ThreeStab2 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le e7Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := (e7ThreeCheck_spec).2 e7ThreeStab3 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le e7Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := (e7ThreeCheck_spec).2 e7ThreeStab4 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le e7Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := (e7ThreeCheck_spec).2 e7ThreeStab5 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le e7Certificate_check hc).trans hp

theorem charStabilizer_eq_kernelWeylGroup_E7_three
    (χ : Multiplicative (Fin Tag.E7.rank → ℤ) →* Z3) :
    charStabilizer χ = kernelWeylGroup χ :=
  charStabilizer_eq_of_card_le_one
    (card_charQuotient_le_of_orbitCheck3 e7ThreeOrbit_check card_kernelPosStabilizer_le_E7_three χ)

theorem rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_three
    {K : Type} [Field K]
    (a : Fin Tag.E7.rank → Kˣ) (h3 : ∀ i, a i ^ 3 = 1) :
    rootCharStabilizerSubgroup a = kernelReflectionGroup a :=
  rootCharStabilizerSubgroup_eq_kernelReflectionGroup_of_triChar
    (fun χ => (charStabilizer_eq_kernelWeylGroup_E7_three χ).le) a h3

end CFSG.HardMathSupport.Timmesfeld.Steinberg
