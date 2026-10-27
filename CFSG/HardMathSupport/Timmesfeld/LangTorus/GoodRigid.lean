module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodRoot
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidTriD4

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

section Untwisted

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem setupRigid_E8_of_goodRoots
    (S : LangSetup .E8 L p) (hp3 : 3 < p) (hAlg : S.IsAlgebraic)
    (hgen : GoodRootsGenerate S) : SetupRigid S :=
  setupRigid_E8 S hp3 hAlg
    (fun _ hD₁ hc => noFrobeniusInner_of_goodRootsGenerate S hgen hD₁ hc)
    (fun _ hD₁ hc => centralizerTrivial_of_goodRoots S hgen hD₁ hc)

theorem setupRigid_E7_of_goodRoots
    (S : LangSetup .E7 L p) (hp3 : 3 < p) (hAlg : S.IsAlgebraic)
    (hgen : GoodRootsGenerate S) : SetupRigid S :=
  setupRigid_E7 S hp3 hAlg
    (fun _ hD₁ hc => noFrobeniusInner_of_goodRootsGenerate S hgen hD₁ hc)
    (fun _ hD₁ hc => centralizerTrivial_of_goodRoots S hgen hD₁ hc)

end Untwisted

section Twisted

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

@[expose] def NoTriCosetCentralizes (τ : Tag) (L : Type) [Field L] (P : ModGL τ L) : Prop :=
  ∀ c ∈ adjointGroup τ L, ∀ a : ℕ, 0 < a → a < 3 →
    ¬ ∀ g ∈ adjointGroup τ L, Commute (c * (P⁻¹) ^ a) g

theorem triCosetEmpty_of_goodRoots {τ : Tag} (S : LangSetup τ L p) (hgen : GoodRootsGenerate S)
    {P : ModGL τ L} (hP : NoTriCosetCentralizes τ L P) {D₁ : Subgroup (ModGL τ L)}
    (hD₁E : D₁ ≤ S.E) (hD₁c : Nat.card D₁ = p ^ 2) : TriCosetEmpty S D₁ P :=
  fun c hc a ha0 ha3 hcomm => hP c hc a ha0 ha3
    (centralizes_adjointGroup_of_goodRoots S hgen hD₁E hD₁c hcomm)

theorem setupRigid_triD4_of_goodRoots
    (S : LangSetup TwistTag.D4.tag L p)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.D4 L Fr)
    (hAlg : S.IsAlgebraic) (hgen : GoodRootsGenerate S)
    (hP : NoTriCosetCentralizes TwistTag.D4.tag L (diagramMap TwistTag.D4 L)) : SetupRigid S :=
  setupRigid_triD4 S hΦ hAlg
    (fun _ hD₁ hc => noFrobeniusInner_of_goodRootsGenerate S hgen hD₁ hc)
    (fun _ hD₁ hc => centralizerTrivial_of_goodRoots S hgen hD₁ hc)
    (fun _ hD₁ hc => triCosetEmpty_of_goodRoots S hgen hP hD₁ hc)

end Twisted

end CFSG.HardMathSupport.Timmesfeld.LangTorus
