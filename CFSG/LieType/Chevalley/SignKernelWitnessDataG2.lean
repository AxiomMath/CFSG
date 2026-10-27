module

public import CFSG.LieType.Chevalley.SignKernelWitnessCert
public import CFSG.LieType.Chevalley.SignStabilizerDataG2

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

@[expose] def g2WitCert0 : WitCert where
  mask := [false, false]
  rho := 0
  sigma := 0
  wits :=
    [⟨0, 1, 1, []⟩, ⟨1, 1, 0, []⟩, ⟨2, 1, 1, []⟩, ⟨3, 1, 0, []⟩, ⟨4, 1, 0, []⟩, ⟨5, 1, 0, []⟩, ⟨6,
      1, 0, []⟩, ⟨7, 1, 0, []⟩, ⟨8, 1, 1, []⟩, ⟨9, 1, 0, []⟩, ⟨10, 1, 0, []⟩, ⟨11, 1, 1, []⟩]

theorem g2WitCert0_check : g2WitCert0.check g2Certificate = true := by
  decide +kernel

@[expose] def g2WitCert1 : WitCert where
  mask := [true, false]
  rho := 0
  sigma := 0
  wits :=
    [⟨1, 0, 0, []⟩, ⟨5, 0, 0, []⟩, ⟨7, 0, 0, []⟩, ⟨10, 0, 0, []⟩]

theorem g2WitCert1_check : g2WitCert1.check g2Certificate = true := by
  decide +kernel

theorem kernelRootWitness_G2
    : ∀ ρ < g2SignReps.length, ∀ α : Fin Tag.G2.rank → ℤ,
    α ∈ kernelRoots (maskChar (listMask (g2SignReps.getD ρ []))) →
      KernelRootWitness (maskChar (listMask (g2SignReps.getD ρ []))) α := by
  intro ρ hρ α hα
  have hlen : g2SignReps.length = 2 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact WitCert.kernelRootWitness_of_check g2Certificate_check g2WitCert0_check
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hα
  · exact WitCert.kernelRootWitness_of_check g2Certificate_check g2WitCert1_check
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hα

end CFSG.LieType.Chevalley
