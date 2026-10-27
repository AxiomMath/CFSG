module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158InnHolds2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158CoreField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def T158FgOmega (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω) (x y : Ω) (J : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ → IsChevSimple 2 (PSimple p S) →
    x ^ p = 1 → y ^ p = 1 → x * y = y * x → x ∉ Subgroup.zpowers y → y ∉ Subgroup.zpowers x →
    InnDiagOn p (Subgroup.zpowers x) S → FieldOn p y S →
    GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J → y ∈ Subgroup.normalizer (J : Set Ω) →
    FGOn p y J

section Inn


theorem t158InnFactOmega_of_fgOmega
    (h : ∀ p, T158FgOmega p) : ∀ p, T158InnFactOmega p :=
  T158Inn.t158InnFactOmega_of_fg T158Core.t158FieldCoreU_holds T158Core.t158TriCore_holds h

end Inn

end CFSG.LocalAnalysis.GLTheoremA.T158

end
