module

public import Certificates.Certificate13691
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharStabilizer

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Steinberg

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem e8ThreeCheck_spec :
    orbitCheck3 .E8 e8ThreeReps e8ThreeOrbit = true ∧
      ∀ S ∈ [e8ThreeStab0, e8ThreeStab1, e8ThreeStab2, e8ThreeStab3, e8ThreeStab4],
        S.check e8Certificate = true ∧ (S.passing e8Certificate).length ≤ 1 := by
  have h := Certificates.certificate13691
  simpa only [e8ThreeCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] using h

theorem e8ThreeOrbit_check :
    orbitCheck3 .E8 e8ThreeReps e8ThreeOrbit = true := (e8ThreeCheck_spec).1

theorem card_kernelPosStabilizer_le_E8_three :
    ∀ ρ < e8ThreeReps.length,
    Nat.card (kernelPosStabilizer (triChar (τ := .E8) (vec3 (e8ThreeReps.getD ρ [])))) ≤ 1 := by
  intro ρ hρ
  have hlen : e8ThreeReps.length = 5 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · obtain ⟨hc, hp⟩ := (e8ThreeCheck_spec).2 e8ThreeStab0 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le e8Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := (e8ThreeCheck_spec).2 e8ThreeStab1 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le e8Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := (e8ThreeCheck_spec).2 e8ThreeStab2 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le e8Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := (e8ThreeCheck_spec).2 e8ThreeStab3 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le e8Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := (e8ThreeCheck_spec).2 e8ThreeStab4 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le e8Certificate_check hc).trans hp

theorem charStabilizer_eq_kernelWeylGroup_E8_three
    (χ : Multiplicative (Fin Tag.E8.rank → ℤ) →* Z3) :
    charStabilizer χ = kernelWeylGroup χ :=
  charStabilizer_eq_of_card_le_one
    (card_charQuotient_le_of_orbitCheck3 e8ThreeOrbit_check card_kernelPosStabilizer_le_E8_three χ)

theorem rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_three
    {K : Type} [Field K]
    (a : Fin Tag.E8.rank → Kˣ) (h3 : ∀ i, a i ^ 3 = 1) :
    rootCharStabilizerSubgroup a = kernelReflectionGroup a :=
  rootCharStabilizerSubgroup_eq_kernelReflectionGroup_of_triChar
    (fun χ => (charStabilizer_eq_kernelWeylGroup_E8_three χ).le) a h3

end CFSG.HardMathSupport.Timmesfeld.Steinberg
