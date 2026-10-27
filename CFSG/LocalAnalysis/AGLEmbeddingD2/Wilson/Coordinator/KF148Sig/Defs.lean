module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig

open Subgroup CFSG.GH74.GLS

@[expose] def InspectSig148 (X : Type) [Group X] (P : Subgroup X → Prop) : Prop :=
  ∀ E K : Subgroup X, Nat.card E = 9 → (∀ x ∈ E, x ^ 3 = 1) →
    E ≤ normalizer (K : Set X) → Group.IsPerfect K → K ≠ ⊥ →
    K ≤ ⨆ (x : X) (_ : x ∈ E) (_ : x ≠ 1), pPrimeCoreOf 3 (K ⊓ centralizer ({x} : Set X)) →
    P K

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig
