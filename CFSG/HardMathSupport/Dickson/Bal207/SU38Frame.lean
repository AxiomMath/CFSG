module

public import CFSG.HardMathSupport.Dickson.Bal207.SU38Reduction

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux

@[expose] def SU38FrameConclusion {X : Type} [Group X] (B J : Subgroup X) : Prop :=
  KSF4SU3.AutImageRankThree B J ∨ SU38Toral B J

@[expose] def SU38FrameSp (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (K B A : Subgroup X),
    Bal207PlusCtx G 3 K B A → IsLieQuot ↥K (FamSp 3) → Bal207PlusIH G A →
      ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
        GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J → IsSU38Comp J →
          B ≤ Subgroup.normalizer (J : Set X) → SU38FrameConclusion B J

@[expose] def SU38FrameUni (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (K B A : Subgroup X),
    Bal207PlusCtx G 3 K B A → IsLieQuot ↥K (FamUni 3) → Bal207PlusIH G A →
      ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
        GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J → IsSU38Comp J →
          B ≤ Subgroup.normalizer (J : Set X) → SU38FrameConclusion B J

@[expose] def SU38FrameOrth (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (K B A : Subgroup X),
    Bal207PlusCtx G 3 K B A → IsLieQuot ↥K (FamOrth 3) → Bal207PlusIH G A →
      ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
        GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J → IsSU38Comp J →
          B ≤ Subgroup.normalizer (J : Set X) → SU38FrameConclusion B J

@[expose] def SU38FrameD4 (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (K B A : Subgroup X),
    Bal207PlusCtx G 3 K B A → IsLieQuot ↥K IsD4EightIdx → NoTrialityOn G B K →
      Bal207PlusIH G A → ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
        GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J → IsSU38Comp J →
          B ≤ Subgroup.normalizer (J : Set X) → SU38FrameConclusion B J

@[expose] def SU38ClassicalFrame (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  SU38FrameSp G ∧ SU38FrameUni G ∧ SU38FrameOrth G ∧ SU38FrameD4 G

end CFSG.HardMathSupport.Dickson.Bal207

end
