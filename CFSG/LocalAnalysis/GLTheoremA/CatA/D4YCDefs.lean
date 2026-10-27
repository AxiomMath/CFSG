module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4TCore
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs122
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4Y

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.D4T

@[expose] def NotCentralOut {K : Type} [Group K] (β : MulAut K) : Prop :=
  ∃ γ : MulAut K, γ * β * γ⁻¹ * β⁻¹ ∉ innerAut K

@[expose] def D4RankCase {H : Type} [Group H] (K B : Subgroup H) : Prop :=
  (∀ P : Subgroup H, IsElemAbelian 3 P → Nat.card P ≤ Nat.card B) ∨
    ((∀ P W : Subgroup H, IsElemAbelian 3 P → IsPGroup 2 W → W ≠ ⊥ →
        P ≤ Subgroup.normalizer (W : Set H) → Nat.card P ≤ Nat.card B) ∧
      ∃ T : Subgroup H, IsPGroup 2 T ∧ T ≠ ⊥ ∧ B ≤ Subgroup.normalizer (T : Set H) ∧
        T ≤ Subgroup.normalizer (K : Set H))

@[expose] def D4BigCoreAt : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (K B : Subgroup H),
    catalogIs ↥K isD4any → ¬ catalogIs ↥K S9.isD4two →
    (∀ k ∈ K, (∀ y ∈ K, y * k = k * y) → k = 1) → IsElemAbelian 3 B →
    B ≤ Subgroup.normalizer (K : Set H) →
    (∃ b ∈ B, ∃ hb : b ∈ Subgroup.normalizer (K : Set H), NotCentralOut (conjAut K b hb)) →
    D4RankCase K B → False

@[expose] def D4BigNormalizes (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X B L : Subgroup G), CFSG.Open.IsKGroup ↥X → IsElemAbelian 3 B → B ≤ X →
    GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 B → GLAPComponent 3 X L →
    catalogIs (PSimple 3 L) isD4any → ¬ catalogIs (PSimple 3 L) S9.isD4two →
    B ≤ Subgroup.normalizer (L : Set G)

end CFSG.LocalAnalysis.GLTheoremA.D4Y
