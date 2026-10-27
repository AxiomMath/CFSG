module

public import CFSG.GF2Type.Smith1980Orth.Four
public import CFSG.LargeExtraspecial.GLRMain
public import CFSG.LargeExtraspecial.S12InspSplit
public import CFSG.LargeExtraspecial.S14Claims
public import CFSG.LargeExtraspecial.S3bTen
public import CFSG.LargeExtraspecial.S4TwoInput
public import CFSG.LargeExtraspecial.S9ThreeMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S14
  CFSG.Open

structure TimInputs : Prop where
  hAS : AschbacherSmithWideInput
  hDW : DW.DW37Statement
  hRI : RootInvolutionComponentsInput.{0}
  hARS : CFSG.Timmesfeld.ARSInput
  hTri : FischerTrialityInput
  hFischer : S12FischerStatement
  hInsp : Insp5Input
  h36 : Timmesfeld36Input
  hSL : S12SL4ModuleInput
  hTI : WeaklyClosedTITransitive.{0}
  hF2 : Form2StrongStmt
  hBen : BenderConjCountInput
  hCE : CentralExtInput.{0}
  h111 : S11_1Stmt
  h118 : S11_8M2Stmt
  hCorB : S8.TimmesfeldCorBInput
  hFacts : S8.CorBListFacts
  h83 : S8_3Stmt
  hRes : S9.Timmesfeld93Residual.{0}
  h9 : S9A6PGLStmt

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem OrthData.exists_conj_mem_Q [IsSimpleGroup G] (hAS : AschbacherSmithWideInput)
    (O : OrthData S) (hw : 5 ≤ S.width) : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z := by
  by_contra hW
  push Not at hW
  obtain ⟨e⟩ := hAS G S hw hW
  have h := FS77.factorization_card_timmesfeldPSU (m := S.width + 2) (by omega)
  rw [← Nat.card_congr e.toEquiv] at h
  exact O.factorization_ne_of_wide hw rfl h

theorem OrthData.not_isReducible [IsSimpleGroup G] (hDW : DW.DW37Statement) (O : OrthData S)
    (hw : 5 ≤ S.width) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    ¬ S.IsReducible := by
  intro hred
  obtain ⟨e⟩ := hDW G S g hw haQ hne hred
  have h := SmithQ.factorization_card_psl (S.width + 2)
  rw [← Nat.card_congr e.toEquiv] at h
  exact O.factorization_ne_of_wide hw rfl h

theorem OrthData.noA2All [IsSimpleGroup G] (I : TimInputs) (O : OrthData S)
    (hw : 5 ≤ S.width) : S11.NoA2All S := by
  intro g haQ hne hA
  obtain ⟨α, hαL, -, hαA⟩ := hA
  have ht : S.ρ α ∈ S.Lbar g := by
    rw [← S.map_La_eq_Lbar g]
    exact ⟨α, mem_subgroupOf.mpr hαL, rfl⟩
  rcases Setting.timmesfeld_12_16_of_insp5 I.hRI I.hARS I.hTri I.hFischer I.hInsp I.h36 I.hSL
      haQ hne hw ht hαA with hred | ⟨h4, -⟩ | hR | ⟨h4, -⟩
  · exact O.not_isReducible I.hDW hw haQ hne hred
  · omega
  · exact Setting.not_s12GammaLResidual haQ hne hw hR
  · omega

end CFSG.GF2Type.Smith1980Orth
