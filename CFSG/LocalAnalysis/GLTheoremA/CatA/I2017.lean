module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017Alt7Orb
public import CFSG.LocalAnalysis.GLTheoremA.S6.AltDefs
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)
open CFSG.LocalAnalysis.GLTheoremA.I2017
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def I2017LieAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K D J I R : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X K →
    D ≤ Subgroup.normalizer (K : Set G) → IsElemAbelian 3 D → Nat.card ↥D = 9 →
    (∃ d ∈ D, d ≠ 1 ∧ CentMod 3 K d) →
    (∀ E : Subgroup G, E ≤ (K ⊔ D) ⊓ Subgroup.centralizer (D : Set G) → IsElemAbelian 3 E →
      Nat.card ↥E ≤ 3 ^ 4) →
    GLAPLayer 3 (K ⊓ Subgroup.centralizer (D : Set G)) = J →
    GLAPComponent 3 (K ⊓ Subgroup.centralizer (D : Set G)) J →
    Nonempty (↥(imageMod 3 K J) ≃* ↥(alternatingGroup (Fin 8))) → I ≤ J →
    Nonempty (↥(imageMod 3 K I) ≃* ↥(alternatingGroup (Fin 7))) → R ≤ K → IsPGroup 2 R →
    I ⊔ D ≤ Subgroup.normalizer (R : Set G) →
    ¬ imageMod 3 K I ≤ Subgroup.centralizer ((imageMod 3 K R : Subgroup (PQuot 3 K)) : Set (PQuot 3 K)) →
    (∃ r : ℕ, r.Prime ∧ catalogIs (PSimple 3 K) (onLie fun d => d.characteristic = r)) →
    IsL62Type 3 K

end CFSG.LocalAnalysis.GLTheoremA
