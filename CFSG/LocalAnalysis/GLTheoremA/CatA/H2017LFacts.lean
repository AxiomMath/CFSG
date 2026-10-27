module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.GLTheoremA.S6.AltDefs
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def gfEightPP : TauCeti.PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩

@[expose] def I2017LieA8Shape (d : TauCeti.LieTypeIndex) : Prop :=
  d = .A 3 gfEightPP ∨ (∃ N : ℕ, 6 ≤ N ∧ Even N ∧ d = .A (N - 1) gfTwoPP) ∨ d = .twistedD 4 gfTwoPP ∨
    ∃ k : ℕ, 5 ≤ k ∧ (d = .D k gfTwoPP ∨ d = .twistedD k gfTwoPP)

@[expose] def I2017LieNoA7Shape (d : TauCeti.LieTypeIndex) : Prop :=
  d = .A 3 gfEightPP ∨ d = .twistedD 4 gfTwoPP

@[expose] def I2017LieRankShape (d : TauCeti.LieTypeIndex) : Prop :=
  (∃ N : ℕ, 8 ≤ N ∧ Even N ∧ d = .A (N - 1) gfTwoPP) ∨
    ∃ k : ℕ, 5 ≤ k ∧ (d = .D k gfTwoPP ∨ d = .twistedD k gfTwoPP)

@[expose] def I2017LieClassification : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
    ∀ (α : MulAut Q) (J : Subgroup Q), α ^ 3 = 1 → α ≠ 1 → GLAPComponent 3 (fixSubgroup α) J →
      IsAltPType 3 J 8 → ∀ d : TauCeti.LieTypeIndex,
        catalogIs (Q ⧸ Subgroup.center Q) (onLie fun d' => d' = d) → I2017LieA8Shape d

@[expose] def I2017LieNoA7 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], catalogIs S (onLie I2017LieNoA7Shape) →
    ∀ T : Subgroup S, IsPGroup 2 T → T ≠ ⊥ → ∀ H : Subgroup S, H ≤ Subgroup.normalizer (T : Set S) →
      ¬ Nonempty (↥H ≃* ↥(alternatingGroup (Fin 7)))

@[expose] def I2017LieRank : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
    ∀ (α : MulAut Q) (J : Subgroup Q), α ^ 3 = 1 → α ≠ 1 → GLAPComponent 3 (fixSubgroup α) J →
      IsAltPType 3 J 8 → catalogIs (Q ⧸ Subgroup.center Q) (onLie I2017LieRankShape) →
        ∃ E : Subgroup Q, E ≤ fixSubgroup α ∧ IsElemAbelian 3 E ∧ Nat.card ↥E = 3 ^ 4

@[expose] def I2017LieCenterL62 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
    catalogIs (Q ⧸ Subgroup.center Q) (onLie fun d => d = .A 5 gfTwoPP) → Subgroup.center Q = ⊥

@[expose] def I2017LieRankCenter : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
    catalogIs (Q ⧸ Subgroup.center Q) (onLie I2017LieRankShape) →
      ∀ z ∈ Subgroup.center Q, z ^ 3 = 1 → z = 1

end CFSG.LocalAnalysis.GLTheoremA
