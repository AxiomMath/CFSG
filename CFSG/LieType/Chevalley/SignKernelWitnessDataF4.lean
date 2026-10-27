module

public import CFSG.LieType.Chevalley.SignKernelWitnessCert
public import CFSG.LieType.Chevalley.SignStabilizerDataF4

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

@[expose] def f4WitCert0 : WitCert where
  mask := [false, false, false, false]
  rho := 47
  sigma := 26
  wits :=
    [⟨0, 1, 1, []⟩, ⟨1, 1, 0, []⟩, ⟨2, 1, 1, []⟩, ⟨3, 1, 2, []⟩, ⟨4, 1, 1, []⟩, ⟨5, 1, 0, []⟩, ⟨6,
      1, 0, []⟩, ⟨7, 1, 0, []⟩, ⟨8, 1, 0, []⟩, ⟨9, 1, 1, []⟩, ⟨10, 1, 1, []⟩, ⟨11, 1, 2, []⟩, ⟨12,
      1, 0, []⟩, ⟨13, 1, 0, []⟩, ⟨14, 1, 0, []⟩, ⟨15, 1, 0, []⟩, ⟨16, 1, 0, []⟩, ⟨17, 1, 0, []⟩,
      ⟨18, 1, 0, []⟩, ⟨19, 1, 1, []⟩, ⟨20, 1, 0, []⟩, ⟨21, 1, 1, []⟩, ⟨22, 1, 0, []⟩, ⟨23, 1, 0,
      []⟩, ⟨24, 1, 0, []⟩, ⟨25, 1, 0, []⟩, ⟨26, 1, 0, []⟩, ⟨27, 1, 0, []⟩, ⟨28, 1, 1, []⟩, ⟨29, 1,
      0, []⟩, ⟨30, 1, 1, []⟩, ⟨31, 1, 0, []⟩, ⟨32, 1, 0, []⟩, ⟨33, 1, 0, []⟩, ⟨34, 1, 1, []⟩, ⟨35,
      1, 1, []⟩, ⟨36, 1, 1, []⟩, ⟨37, 1, 0, []⟩, ⟨38, 1, 1, []⟩, ⟨39, 1, 0, []⟩, ⟨40, 1, 2, []⟩,
      ⟨41, 1, 1, []⟩, ⟨42, 1, 0, []⟩, ⟨43, 1, 0, []⟩, ⟨44, 1, 3, []⟩, ⟨45, 1, 2, []⟩, ⟨46, 1, 0,
      []⟩, ⟨47, 1, 3, []⟩]

theorem f4WitCert0_check : f4WitCert0.check f4Certificate = true := by
  decide +kernel

@[expose] def f4WitCert1 : WitCert where
  mask := [true, false, false, false]
  rho := 47
  sigma := 26
  wits :=
    [⟨1, 2, 0, [1, 2, 0, 1, 2, 3, 2, 1, 0]⟩, ⟨2, 1, 1, []⟩, ⟨3, 1, 2, []⟩, ⟨6, 2, 0, [2, 0, 1, 2, 3,
      2, 1, 0]⟩, ⟨7, 2, 0, [2, 1, 2, 0, 1, 2, 3, 2, 1, 0]⟩, ⟨8, 1, 1, []⟩, ⟨9, 1, 1, []⟩, ⟨10, 1, 1,
      []⟩, ⟨11, 1, 2, []⟩, ⟨14, 2, 0, [0, 1, 2, 3, 2, 1, 0]⟩, ⟨15, 2, 0, [3, 2, 1, 2, 0, 1, 2, 3, 2,
      1, 0]⟩, ⟨17, 1, 1, []⟩, ⟨18, 1, 1, []⟩, ⟨19, 1, 1, []⟩, ⟨23, 2, 0, [0, 1, 2, 3, 1, 0]⟩, ⟨25,
      1, 2, []⟩, ⟨27, 1, 1, []⟩, ⟨33, 1, 2, []⟩, ⟨43, 0, 0, []⟩, ⟨46, 0, 0, []⟩]

theorem f4WitCert1_check : f4WitCert1.check f4Certificate = true := by
  decide +kernel

@[expose] def f4WitCert2 : WitCert where
  mask := [false, false, true, false]
  rho := 47
  sigma := 26
  wits :=
    [⟨0, 1, 1, []⟩, ⟨1, 1, 0, []⟩, ⟨3, 1, 7, []⟩, ⟨4, 1, 1, []⟩, ⟨5, 1, 0, []⟩, ⟨6, 1, 0, []⟩, ⟨7,
      1, 0, []⟩, ⟨11, 1, 7, []⟩, ⟨12, 1, 0, []⟩, ⟨13, 1, 0, []⟩, ⟨14, 1, 0, []⟩, ⟨15, 1, 0, []⟩,
      ⟨20, 1, 0, []⟩, ⟨21, 1, 1, []⟩, ⟨22, 1, 0, []⟩, ⟨23, 1, 0, []⟩, ⟨25, 1, 0, []⟩, ⟨28, 1, 1,
      []⟩, ⟨29, 1, 0, []⟩, ⟨30, 1, 1, []⟩, ⟨31, 1, 0, []⟩, ⟨33, 1, 0, []⟩, ⟨34, 1, 1, []⟩, ⟨35, 1,
      1, []⟩, ⟨36, 1, 1, []⟩, ⟨37, 1, 0, []⟩, ⟨38, 1, 1, []⟩, ⟨39, 1, 0, []⟩, ⟨41, 1, 1, []⟩, ⟨42,
      1, 0, []⟩, ⟨43, 1, 0, []⟩, ⟨46, 1, 0, []⟩]

theorem f4WitCert2_check : f4WitCert2.check f4Certificate = true := by
  decide +kernel

theorem f4Certificate_root_rho : f4Certificate.root 47 = f4Rho := by
  funext j
  fin_cases j <;> decide +kernel

theorem f4Certificate_root_sigma : f4Certificate.root 26 = f4Sigma := by
  funext j
  fin_cases j <;> decide +kernel

theorem kernelRootWitness_F4
    : ∀ ρ < f4SignReps.length, ∀ α : Fin Tag.F4.rank → ℤ,
    α ∈ kernelRoots (maskChar (listMask (f4SignReps.getD ρ []))) →
      KernelRootWitness (maskChar (listMask (f4SignReps.getD ρ []))) α := by
  intro ρ hρ α hα
  have hlen : f4SignReps.length = 3 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact WitCert.kernelRootWitness_of_check f4Certificate_check f4WitCert0_check
      (fun _ => f4Certificate_root_rho) (fun _ => f4Certificate_root_sigma) hα
  · exact WitCert.kernelRootWitness_of_check f4Certificate_check f4WitCert1_check
      (fun _ => f4Certificate_root_rho) (fun _ => f4Certificate_root_sigma) hα
  · exact WitCert.kernelRootWitness_of_check f4Certificate_check f4WitCert2_check
      (fun _ => f4Certificate_root_rho) (fun _ => f4Certificate_root_sigma) hα

end CFSG.LieType.Chevalley
