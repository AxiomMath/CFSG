module

public import CFSG.RankThree.PartOne.S11d.Facts5
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.StrongCover
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def ReeF4Idx : TauCeti.LieTypeIndex → Prop := fun i => ∃ k : ℕ, i = .reeF4 k

@[expose] def LargeReeCentralizerActsInner : Prop :=
  ∀ (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid) {S : Type} [Group S] [Finite S]
    (_ : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (x : S) (hx : orderOf x = p) (N : Subgroup S),
    N ≤ Subgroup.centralizer ({x} : Set S) →
    (∀ g ∈ Subgroup.centralizer ({x} : Set S), (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ N) →
    (∀ D : Subgroup S,
      CFSG.RankThree.PartOne.IsComponentOf (Subgroup.centralizer ({x} : Set S)) D → D = N) →
    (N ≠ ⊥ →
      CFSG.RankThree.PartOne.IsComponentOf (Subgroup.centralizer ({x} : Set S)) N) →
    ∀ c ∈ Subgroup.centralizer ({x} : Set S),
      ∃ n ∈ N, ∀ y ∈ N, c * y * c⁻¹ = n * y * n⁻¹

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
