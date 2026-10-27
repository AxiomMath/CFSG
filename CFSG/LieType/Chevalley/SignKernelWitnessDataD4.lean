module

public import CFSG.LieType.Chevalley.SignKernelWitnessCert
public import CFSG.LieType.Chevalley.SignStabilizerDataD4

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

@[expose] def d4WitCert0 : WitCert where
  mask := [false, false, false, false]
  rho := 0
  sigma := 0
  wits :=
    [⟨0, 1, 2, []⟩, ⟨1, 1, 2, []⟩, ⟨2, 1, 0, []⟩, ⟨3, 1, 2, []⟩, ⟨4, 1, 2, []⟩, ⟨5, 1, 0, []⟩, ⟨6,
      1, 2, []⟩, ⟨7, 1, 0, []⟩, ⟨8, 1, 0, []⟩, ⟨9, 1, 0, []⟩, ⟨10, 1, 2, []⟩, ⟨11, 1, 0, []⟩, ⟨12,
      1, 0, []⟩, ⟨13, 1, 0, []⟩, ⟨14, 1, 0, []⟩, ⟨15, 1, 0, []⟩, ⟨16, 1, 0, []⟩, ⟨17, 1, 0, []⟩,
      ⟨18, 1, 0, []⟩, ⟨19, 1, 0, []⟩, ⟨20, 1, 0, []⟩, ⟨21, 1, 0, []⟩, ⟨22, 1, 2, []⟩, ⟨23, 1, 2,
      []⟩]

theorem d4WitCert0_check : d4WitCert0.check d4Certificate = true := by
  decide +kernel

@[expose] def d4WitCert1 : WitCert where
  mask := [true, false, false, false]
  rho := 0
  sigma := 0
  wits :=
    [⟨1, 1, 2, []⟩, ⟨2, 1, 1, []⟩, ⟨3, 1, 2, []⟩, ⟨6, 1, 2, []⟩, ⟨7, 1, 1, []⟩, ⟨8, 1, 1, []⟩, ⟨9,
      1, 1, []⟩, ⟨10, 1, 2, []⟩, ⟨14, 1, 1, []⟩, ⟨15, 1, 1, []⟩, ⟨16, 1, 1, []⟩, ⟨20, 1, 1, []⟩]

theorem d4WitCert1_check : d4WitCert1.check d4Certificate = true := by
  decide +kernel

@[expose] def d4WitCert2 : WitCert where
  mask := [false, true, false, false]
  rho := 0
  sigma := 0
  wits :=
    [⟨0, 1, 2, []⟩, ⟨2, 1, 0, []⟩, ⟨3, 1, 2, []⟩, ⟨4, 1, 2, []⟩, ⟨5, 1, 0, []⟩, ⟨8, 1, 0, []⟩, ⟨9,
      1, 0, []⟩, ⟨10, 1, 2, []⟩, ⟨11, 1, 0, []⟩, ⟨13, 1, 0, []⟩, ⟨16, 1, 0, []⟩, ⟨18, 1, 0, []⟩]

theorem d4WitCert2_check : d4WitCert2.check d4Certificate = true := by
  decide +kernel

@[expose] def d4WitCert3 : WitCert where
  mask := [true, true, false, false]
  rho := 0
  sigma := 0
  wits :=
    [⟨2, 1, 3, []⟩, ⟨3, 1, 2, []⟩, ⟨8, 1, 3, []⟩, ⟨9, 1, 2, []⟩, ⟨10, 1, 2, []⟩, ⟨12, 1, 3, []⟩,
      ⟨16, 1, 2, []⟩, ⟨17, 1, 3, []⟩, ⟨19, 1, 2, []⟩, ⟨21, 1, 2, []⟩, ⟨22, 1, 2, []⟩, ⟨23, 1, 2,
      []⟩]

theorem d4WitCert3_check : d4WitCert3.check d4Certificate = true := by
  decide +kernel

@[expose] def d4WitCert4 : WitCert where
  mask := [false, false, true, false]
  rho := 0
  sigma := 0
  wits :=
    [⟨0, 0, 0, []⟩, ⟨1, 0, 0, []⟩, ⟨3, 0, 0, []⟩, ⟨4, 0, 0, []⟩, ⟨6, 0, 0, []⟩, ⟨10, 0, 0, []⟩, ⟨22,
      0, 0, []⟩, ⟨23, 0, 0, []⟩]

theorem d4WitCert4_check : d4WitCert4.check d4Certificate = true := by
  decide +kernel

theorem kernelRootWitness_D4
    : ∀ ρ < d4SignReps.length, ∀ α : Fin Tag.D4.rank → ℤ,
    α ∈ kernelRoots (maskChar (listMask (d4SignReps.getD ρ []))) →
      KernelRootWitness (maskChar (listMask (d4SignReps.getD ρ []))) α := by
  intro ρ hρ α hα
  have hlen : d4SignReps.length = 5 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact WitCert.kernelRootWitness_of_check d4Certificate_check d4WitCert0_check
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hα
  · exact WitCert.kernelRootWitness_of_check d4Certificate_check d4WitCert1_check
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hα
  · exact WitCert.kernelRootWitness_of_check d4Certificate_check d4WitCert2_check
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hα
  · exact WitCert.kernelRootWitness_of_check d4Certificate_check d4WitCert3_check
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hα
  · exact WitCert.kernelRootWitness_of_check d4Certificate_check d4WitCert4_check
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hα

end CFSG.LieType.Chevalley
