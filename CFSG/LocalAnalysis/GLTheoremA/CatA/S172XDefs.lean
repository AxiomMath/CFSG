module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def LayerIs (p : ℕ) {G : Type} [Group G] (X : Subgroup G) (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  IsComponentOf (GLALayer X) X ∧ catalogIs (PSimple p (GLALayer X)) Q

@[expose] def LiftableRank (p : ℕ) (G₀ : Type) [Group G₀] (m : ℕ) : Prop :=
  (∀ E : Subgroup G₀, IsElemAbelian p E → Nat.card E ≤ p ^ m) ∧
  ∃ (e t : Fin m → G₀) (T : Subgroup G₀),
    IsElemAbelian p (Subgroup.closure (Set.range e)) ∧
    Nat.card (Subgroup.closure (Set.range e)) = p ^ m ∧
    (∀ i, t i ^ 2 = 1 ∧ t i * e i * (t i)⁻¹ = (e i)⁻¹) ∧
    (∀ i j, i ≠ j → t i * e j = e j * t i) ∧
    IsPGroup 2 T ∧ T ≠ ⊥ ∧
    Subgroup.closure (Set.range e) ≤ Subgroup.normalizer (T : Set G₀)

@[expose] def ModelExist (p : ℕ) (G₀ : Type) [Group G₀] (m : ℕ)
    (QK Q₁ Q₂ : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ Bb : Subgroup G₀, IsElemAbelian p Bb → Nat.card Bb = p ^ m →
    ∀ d ∈ Bb, LayerIs p (Subgroup.centralizer {d}) QK →
      Bb ⊓ Subgroup.centralizer (GLALayer (Subgroup.centralizer {d}) : Set G₀) = Subgroup.zpowers d →
      ∃ y ∈ Bb, y ∉ Subgroup.zpowers d ∧ LayerIs p (Subgroup.centralizer {y}) Q₁ ∧
        Bb ⊓ Subgroup.centralizer (GLALayer (Subgroup.centralizer {y}) : Set G₀) = Subgroup.zpowers y ∧
        LayerIs p (Subgroup.centralizer {d, y}) Q₂

@[expose] def ModelSolvable (p : ℕ) (G₀ : Type) [Group G₀] (m : ℕ) (QK : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ Bb : Subgroup G₀, IsElemAbelian p Bb → Nat.card Bb = p ^ m →
    ∀ d ∈ Bb, LayerIs p (Subgroup.centralizer {d}) QK →
      Bb ⊓ Subgroup.centralizer (GLALayer (Subgroup.centralizer {d}) : Set G₀) = Subgroup.zpowers d →
      ∀ e ∈ Bb, e ∉ Subgroup.zpowers d → IsSolvable ↥(Subgroup.centralizer ({d, e} : Set G₀))

end CFSG.LocalAnalysis.GLTheoremA.S172X

end
