module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def IsHatSix (X : Type*) [Group X] : Prop :=
  commutator X = ⊤ ∧ Nat.card (Subgroup.center X) = 3 ∧
    Nonempty ((X ⧸ Subgroup.center X) ≃* ↥(alternatingGroup (Fin 6)))

@[expose] def IsSporadicOf (S : TauCeti.SporadicName) (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* (TauCeti.CFSGIndex.sporadic S).Group)

@[expose] def IsMJRType (X : Type*) [Group X] : Prop :=
  IsSporadicOf TauCeti.SporadicName.M24 X ∨ IsSporadicOf TauCeti.SporadicName.J2 X ∨
    IsSporadicOf TauCeti.SporadicName.Ru X

@[expose] def GapFinalLayerON : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsHatON Y → ∀ α : MulAut Y, α ^ 3 = 1 →
    (∃ J : Subgroup Y, GLAPComponent 3 (Lemma510Ns.fixSub α) J) ∧
    ∀ J : Subgroup Y, GLAPComponent 3 (Lemma510Ns.fixSub α) J →
      Subgroup.center Y ≤ J ∧ (IsHatON (barOf 3 J) ∨ IsHatSix (barOf 3 J))

@[expose] def GapFinalKType : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B' : Subgroup G, IsBOneMax 3 B' → ∀ b ∈ B', b ≠ 1 → ∀ L : Subgroup G,
      GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L → IsHatON (barOf 3 L) → b ∈ L →
      B' ≤ Subgroup.normalizer (L : Set G) → ∀ a ∈ B', a ∉ Subgroup.zpowers b →
      ∀ J : Subgroup G, GLAPComponent 3 (L ⊓ Subgroup.centralizer ({a} : Set G)) J →
        (IsHatON (barOf 3 J) ∨ IsHatSix (barOf 3 J)) → b ∈ J →
        GLAPComponent 3 (Subgroup.centralizer ({a} : Set G)) (Lemma512Ns.conjHull a J) →
          b ∈ oPrimePOf 3 (Lemma512Ns.conjHull a J) ∨ IsMJRType (barOf 3 (Lemma512Ns.conjHull a J))

@[expose] def GapFinalSetup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B' : Subgroup G, IsBOneMax 3 B' → ∀ b ∈ B', b ≠ 1 → ∀ L : Subgroup G,
      GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L → IsHatON (barOf 3 L) → b ∈ L →
      B' ≤ Subgroup.normalizer (L : Set G) → ∀ a ∈ B', a ∉ Subgroup.zpowers b →
        ∃ J : Subgroup G, GLAPComponent 3 (L ⊓ Subgroup.centralizer ({a} : Set G)) J ∧
          (IsHatON (barOf 3 J) ∨ IsHatSix (barOf 3 J)) ∧ b ∈ J ∧
          GLAPComponent 3 (Subgroup.centralizer ({a} : Set G)) (Lemma512Ns.conjHull a J)

@[expose] def GapFinalBalance : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsMJRType X → CFSG.HardMathSupport.Timmesfeld.Coordinator.IsLocallyBalancedAbs 3 2 X

end CFSG.HardMathSupport.Solomon.Coordinator
