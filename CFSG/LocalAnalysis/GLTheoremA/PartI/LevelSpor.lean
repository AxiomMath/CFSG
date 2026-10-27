module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1412
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def KDSporRow (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
  (k2 p (TauCeti.CFSGIndex.sporadic s) → DownLe p 2 (TauCeti.CFSGIndex.sporadic s).Group) ∧
    (k3 p (TauCeti.CFSGIndex.sporadic s) → DownLe p 3 (TauCeti.CFSGIndex.sporadic s).Group)

@[expose] def KDSporRowLive (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
  k2Spor p s ∨ (p = 3 ∧ (s = .M12 ∨ s = .M22))

theorem kdSporRow_of_not {s : TauCeti.SporadicName} {p : ℕ} (h : ¬ KDSporRowLive s p) :
    KDSporRow s p := by
  refine ⟨fun h2 => (h (Or.inl h2)).elim, fun h3 => (h (Or.inr h3)).elim⟩

end CFSG.LocalAnalysis.GLTheoremA
