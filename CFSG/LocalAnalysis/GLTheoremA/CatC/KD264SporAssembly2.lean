module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporM23
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporHS

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen

open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable)

@[expose] def KD264SporResidual2 : Prop :=
  (∀ p, p.Prime → p ≠ 2 → KD264SporAt p .M) ∧ KD264SporAt 7 .B ∧
    KD264SporAt 3 .Co1 ∧ KD264SporAt 5 .Co1 ∧ KD264SporAt 7 .Co1 ∧ KD264SporAt 3 .HN ∧
    KD264SporAt 7 .Th


theorem kd264SporResidual_of_residual2
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : SporadicOrdersTable)
    (hsimple : ∀ s : TauCeti.SporadicName, s ≠ .M → Finite (Carrier s) ∧ IsSimpleGroup (Carrier s))
    (hres : KD264SporResidual2) : KD264SporResidual := by
  obtain ⟨hM, hB7, hCo13, hCo15, hCo17, hHN3, hTh7⟩ := hres
  exact ⟨hM, hB7, hCo13, hCo15, hCo17, hHN3, hTh7,
    CFSG.LocalAnalysis.GLTheoremA.KD264M23.kd264SporAt_M23_three hOut hbr hOrd
      (hsimple .M23 (by decide)),
    CFSG.LocalAnalysis.GLTheoremA.KD264HS.kd264SporAt_HS_three hOut hbr (hsimple .HS (by decide)).2,
    kd264SporAt_M24_three hOut hbr hOrd (hsimple .M24 (by decide)),
    kd264SporAt_J4_three hOut hbr hOrd (hsimple .J4 (by decide)) (hsimple .M22 (by decide)).2,
    kd264SporAt_Ru_three hOut hbr hOrd (hsimple .Ru (by decide)),
    kd264RowData_J2_three, kd264RowData_He_three⟩

theorem kd264SporS_of_residual2
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : SporadicOrdersTable)
    (hsimple : ∀ s : TauCeti.SporadicName, s ≠ .M → Finite (Carrier s) ∧ IsSimpleGroup (Carrier s))
    (hres : KD264SporResidual2) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : KD264SporS p :=
  kd264SporS_of_residual hOut hbr hOrd hsimple
    (kd264SporResidual_of_residual2 hOut hbr hOrd hsimple hres) p hp hp2

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen
