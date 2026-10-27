module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

open scoped commutatorElement

@[expose] def I1416Chev2SporS : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (s : TauCeti.SporadicName),
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ β : MulAut S, β ^ p = 1 → β ≠ 1 → ∀ K : Subgroup S,
      GLAPComponent p (fixSubgroup β) K → IsChevSimple 2 (PSimple p K) → 6 ≤ twoRank ↥K → False

@[expose] def chev2Small : TauCeti.CFSGIndex → Prop
  | .alternating n _ => n = 5 ∨ n = 6 ∨ n = 8
  | .lie i =>
    match i.1 with
    | .A 1 q => q.card = 7 ∨ q.card = 8
    | .twistedA 2 q => q.card = 3
    | .twistedA 3 q => q.card = 2
    | _ => False
  | _ => False

@[expose] def Chev2BridgeAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (Y J : Subgroup G), p.Prime → GLAPComponent p Y J → IsChev2 J → IsChevSimple 2 (PSimple p J)

@[expose] def Chev2OddAmb : Prop :=
  ∀ (r : ℕ) (T : Type) [Group T], r.Prime → r ≠ 2 → IsChevSimple 2 T → IsChevSimple r T → catalogIs T chev2Small

theorem pQuot_equiv_of_centMod {G : Type} [Group G] [Finite G] {p : ℕ} {X K J : Subgroup G} {y : G}
    (hp : p.Prime) (hK : GLAPComponent p X K) (hy : IsPGroup p (Subgroup.zpowers y))
    (hCM : CentMod p K y) (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set G)) J) :
    Nonempty (PQuot p J ≃* PQuot p K) := by
  set C : Subgroup G := K ⊓ Subgroup.centralizer ({y} : Set G) with hCdef
  have hCK : C ⊔ GLAPPrimeCoreOf p K = K := inf_centralizer_sup_eq_of_centMod hp hy hCM
  obtain ⟨hcov, ⟨eC⟩⟩ := cover_facts hp (inf_le_left : C ≤ K) hCK
  have hqK : CFSG.Open.IsQuasisimple (PQuot p K) := isQuasisimple_pQuot_of_glaPComponent hp hK
  have hqC : CFSG.Open.IsQuasisimple (PQuot p C) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eC.symm hqK
  obtain ⟨-, hlay, hbar⟩ := glaPLayer_of_isQuasisimple hqC
  have hJeq : J = GLAPLayer p C := hlay J hJ
  have hbarJ : barX p C J = ⊤ := hJeq ▸ hbar
  have hJcov : J ⊔ GLAPPrimeCoreOf p C = C := sup_glaPPrimeCoreOf_eq_of_barX_eq_top hJ.1 hbarJ
  have hOC : GLAPPrimeCoreOf p C ≤ GLAPPrimeCoreOf p K := by
    rw [hcov]
    exact inf_le_right
  have hJK : J ⊔ GLAPPrimeCoreOf p K = K := by
    apply le_antisymm
    · exact sup_le (hJ.1.trans inf_le_left) (Subgroup.map_subtype_le _)
    · calc K = C ⊔ GLAPPrimeCoreOf p K := hCK.symm
        _ ≤ J ⊔ GLAPPrimeCoreOf p K := by
          apply sup_le _ le_sup_right
          calc C = J ⊔ GLAPPrimeCoreOf p C := hJcov.symm
            _ ≤ J ⊔ GLAPPrimeCoreOf p K := sup_le_sup_left hOC J
  exact (cover_facts hp (hJ.1.trans inf_le_left) hJK).2

end CFSG.LocalAnalysis.GLTheoremA
