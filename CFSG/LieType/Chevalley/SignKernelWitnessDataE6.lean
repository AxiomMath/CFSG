module

public import CFSG.LieType.Chevalley.SignKernelWitnessCert
public import CFSG.LieType.Chevalley.SignStabilizerDataE6

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

@[expose] def e6WitCert0 : WitCert where
  mask := [false, false, false, false, false, false]
  rho := 0
  sigma := 0
  wits :=
    [⟨0, 1, 2, []⟩, ⟨1, 1, 3, []⟩, ⟨2, 1, 0, []⟩, ⟨3, 1, 1, []⟩, ⟨4, 1, 3, []⟩, ⟨5, 1, 4, []⟩, ⟨6,
      1, 2, []⟩, ⟨7, 1, 0, []⟩, ⟨8, 1, 3, []⟩, ⟨9, 1, 1, []⟩, ⟨10, 1, 0, []⟩, ⟨11, 1, 0, []⟩, ⟨12,
      1, 1, []⟩, ⟨13, 1, 1, []⟩, ⟨14, 1, 3, []⟩, ⟨15, 1, 3, []⟩, ⟨16, 1, 4, []⟩, ⟨17, 1, 0, []⟩,
      ⟨18, 1, 0, []⟩, ⟨19, 1, 1, []⟩, ⟨20, 1, 0, []⟩, ⟨21, 1, 1, []⟩, ⟨22, 1, 0, []⟩, ⟨23, 1, 0,
      []⟩, ⟨24, 1, 1, []⟩, ⟨25, 1, 1, []⟩, ⟨26, 1, 3, []⟩, ⟨27, 1, 0, []⟩, ⟨28, 1, 0, []⟩, ⟨29, 1,
      0, []⟩, ⟨30, 1, 0, []⟩, ⟨31, 1, 1, []⟩, ⟨32, 1, 0, []⟩, ⟨33, 1, 1, []⟩, ⟨34, 1, 0, []⟩, ⟨35,
      1, 0, []⟩, ⟨36, 1, 1, []⟩, ⟨37, 1, 0, []⟩, ⟨38, 1, 0, []⟩, ⟨39, 1, 0, []⟩, ⟨40, 1, 0, []⟩,
      ⟨41, 1, 0, []⟩, ⟨42, 1, 1, []⟩, ⟨43, 1, 0, []⟩, ⟨44, 1, 0, []⟩, ⟨45, 1, 0, []⟩, ⟨46, 1, 0,
      []⟩, ⟨47, 1, 0, []⟩, ⟨48, 1, 0, []⟩, ⟨49, 1, 0, []⟩, ⟨50, 1, 0, []⟩, ⟨51, 1, 0, []⟩, ⟨52, 1,
      0, []⟩, ⟨53, 1, 0, []⟩, ⟨54, 1, 0, []⟩, ⟨55, 1, 2, []⟩, ⟨56, 1, 0, []⟩, ⟨57, 1, 0, []⟩, ⟨58,
      1, 0, []⟩, ⟨59, 1, 2, []⟩, ⟨60, 1, 0, []⟩, ⟨61, 1, 2, []⟩, ⟨62, 1, 0, []⟩, ⟨63, 1, 0, []⟩,
      ⟨64, 1, 2, []⟩, ⟨65, 1, 0, []⟩, ⟨66, 1, 2, []⟩, ⟨67, 1, 2, []⟩, ⟨68, 1, 1, []⟩, ⟨69, 1, 1,
      []⟩, ⟨70, 1, 1, []⟩, ⟨71, 1, 1, []⟩]

theorem e6WitCert0_check : e6WitCert0.check e6Certificate = true := by
  decide +kernel

@[expose] def e6WitCert1 : WitCert where
  mask := [true, false, false, false, false, false]
  rho := 0
  sigma := 0
  wits :=
    [⟨1, 1, 3, []⟩, ⟨2, 1, 3, []⟩, ⟨3, 1, 1, []⟩, ⟨4, 1, 3, []⟩, ⟨5, 1, 4, []⟩, ⟨8, 1, 3, []⟩, ⟨9,
      1, 1, []⟩, ⟨10, 1, 3, []⟩, ⟨11, 1, 1, []⟩, ⟨12, 1, 1, []⟩, ⟨13, 1, 1, []⟩, ⟨14, 1, 3, []⟩,
      ⟨15, 1, 3, []⟩, ⟨16, 1, 4, []⟩, ⟨19, 1, 1, []⟩, ⟨20, 1, 1, []⟩, ⟨21, 1, 1, []⟩, ⟨22, 1, 1,
      []⟩, ⟨23, 1, 1, []⟩, ⟨24, 1, 1, []⟩, ⟨25, 1, 1, []⟩, ⟨26, 1, 3, []⟩, ⟨30, 1, 1, []⟩, ⟨31, 1,
      1, []⟩, ⟨32, 1, 1, []⟩, ⟨33, 1, 1, []⟩, ⟨34, 1, 1, []⟩, ⟨35, 1, 1, []⟩, ⟨36, 1, 1, []⟩, ⟨41,
      1, 1, []⟩, ⟨42, 1, 1, []⟩, ⟨43, 1, 3, []⟩, ⟨44, 1, 1, []⟩, ⟨45, 1, 1, []⟩, ⟨50, 1, 3, []⟩,
      ⟨51, 1, 1, []⟩, ⟨52, 1, 3, []⟩, ⟨57, 1, 3, []⟩, ⟨58, 1, 4, []⟩, ⟨63, 1, 4, []⟩]

theorem e6WitCert1_check : e6WitCert1.check e6Certificate = true := by
  decide +kernel

@[expose] def e6WitCert2 : WitCert where
  mask := [false, true, false, false, false, false]
  rho := 0
  sigma := 0
  wits :=
    [⟨0, 1, 2, []⟩, ⟨2, 1, 0, []⟩, ⟨3, 1, 2, []⟩, ⟨4, 1, 3, []⟩, ⟨5, 1, 4, []⟩, ⟨6, 1, 2, []⟩, ⟨7,
      1, 0, []⟩, ⟨10, 1, 0, []⟩, ⟨11, 1, 0, []⟩, ⟨12, 1, 2, []⟩, ⟨13, 1, 2, []⟩, ⟨14, 1, 3, []⟩,
      ⟨15, 1, 3, []⟩, ⟨16, 1, 4, []⟩, ⟨17, 1, 0, []⟩, ⟨18, 1, 0, []⟩, ⟨22, 1, 0, []⟩, ⟨23, 1, 0,
      []⟩, ⟨24, 1, 2, []⟩, ⟨25, 1, 2, []⟩, ⟨26, 1, 3, []⟩, ⟨27, 1, 0, []⟩, ⟨29, 1, 0, []⟩, ⟨34, 1,
      0, []⟩, ⟨35, 1, 0, []⟩, ⟨36, 1, 2, []⟩, ⟨38, 1, 0, []⟩, ⟨40, 1, 0, []⟩, ⟨45, 1, 0, []⟩, ⟨47,
      1, 0, []⟩, ⟨70, 0, 0, []⟩, ⟨71, 0, 0, []⟩]

theorem e6WitCert2_check : e6WitCert2.check e6Certificate = true := by
  decide +kernel

theorem kernelRootWitness_E6
    : ∀ ρ < e6SignReps.length, ∀ α : Fin Tag.E6.rank → ℤ,
    α ∈ kernelRoots (maskChar (listMask (e6SignReps.getD ρ []))) →
      KernelRootWitness (maskChar (listMask (e6SignReps.getD ρ []))) α := by
  intro ρ hρ α hα
  have hlen : e6SignReps.length = 3 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact WitCert.kernelRootWitness_of_check e6Certificate_check e6WitCert0_check
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hα
  · exact WitCert.kernelRootWitness_of_check e6Certificate_check e6WitCert1_check
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hα
  · exact WitCert.kernelRootWitness_of_check e6Certificate_check e6WitCert2_check
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hα

end CFSG.LieType.Chevalley
