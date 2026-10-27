module

public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

@[expose] def L9_8GenSTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaGen Ω →
    ∀ K ∈ Ω, ∀ J ∈ Ω, InA Ω K J → ∀ z j : G, IsUniqueInvolution K z → IsUniqueInvolution J j →
      ∀ K' ∈ Ω, K' ≠ K → twinSet Ω K = {K, K'} →
        ∀ Xg : Subgroup G, IsPGroup 2 Xg →
          Xg ≤ Subgroup.centralizer ({z, j} : Set G) →
          ∀ P : Subgroup G,
            IsSylow2In P ((K ⊔ K') ⊔ (J ⊓ Subgroup.centralizer ({z} : Set G))) →
            (∀ x ∈ Xg, conjSub x P = P) →
            ∀ S : Sylow 2 G, P ⊔ Xg ≤ (S : Subgroup G) →
            2 < Nat.card ↥(J ⊓ (S : Subgroup G)) →
            ∀ W ∈ WSet Ω, W ≤ (S : Subgroup G) →
              ((∀ x ∈ Xg, conjSub x K = K) ↔ (∀ x ∈ Xg, conjSub x J = J)) ∧
              ((∀ x ∈ Xg, ∀ w ∈ W ⊓ K, x * w = w * x) →
                ∃ A : Subgroup G,
                  ((W ⊓ J) ⊔ (W ⊓ K)) ⊔ Xg = ((W ⊓ J) ⊔ (W ⊓ K)) ⊔ A ∧
                  ((W ⊓ J) ⊔ (W ⊓ K)) ⊓ A = ⊥ ∧
                  (∀ a ∈ A, ∀ y ∈ (W ⊓ J) ⊔ (W ⊓ K), a * y = y * a) ∧
                  A ≤ centralizerModOdd ⊤ (K ⊔ K') ∧ A ≤ centralizerModOdd ⊤ J)

end CFSG.ClassicalInvolution.Disconnected.AschTight
