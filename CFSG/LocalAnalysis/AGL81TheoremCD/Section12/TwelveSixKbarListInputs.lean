module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatalogue
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixTInvariant
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.LocalAnalysis.AGL81I.Section3 (KGroupLowRank24_12)

@[expose] def KFactKbarListThree : Prop :=
  ∀ (K : Type) [Group K] [Finite K], KGroupLowRank24_12 3 K →
    CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 3 →
    ∀ (S : Type) [Group S] [Finite S], Nonempty (K ⧸ Subgroup.center K ≃* S) →
    ∀ (Y V W₁ W₂ W₃ : Subgroup (MulAut S)) (t₁ t₂ t₃ : MulAut S),
      (MulAut.conj : S →* MulAut S).range ≤ Y → CFSG.Open.pRank 3 Y ≤ 3 →
      IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃ → V ≤ Y → t₁ ∈ Y → t₂ ∈ Y → t₃ ∈ Y →
      LieModel S .PSL 2 3 3 ∨ LieModel S .PSp 2 3 1 ∨ LieModel S .PSp 3 2 1 ∨
        Nonempty (S ≃* alternatingGroup (Fin 9)) ∨ Nonempty (S ≃* alternatingGroup (Fin 10)) ∨
        Nonempty (S ≃* alternatingGroup (Fin 11)) ∨ IsSporadic S .J3

@[expose] def KFactKbarListFive : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p →
    ∀ (K : Type) [Group K] [Finite K], KGroupLowRank24_12 p K →
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 3 →
    ∀ (S : Type) [Group S] [Finite S], Nonempty (K ⧸ Subgroup.center K ≃* S) →
    ∀ (Y V W₁ W₂ W₃ : Subgroup (MulAut S)) (t₁ t₂ t₃ : MulAut S),
      (MulAut.conj : S →* MulAut S).range ≤ Y → CFSG.Open.pRank 3 Y ≤ 3 →
      IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃ → V ≤ Y → t₁ ∈ Y → t₂ ∈ Y → t₃ ∈ Y →
      p = 5 ∧ Nonempty (S ≃* alternatingGroup (Fin 10))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
