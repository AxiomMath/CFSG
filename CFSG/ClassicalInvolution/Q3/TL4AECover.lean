module

public import CFSG.ClassicalInvolution.Q3.TL3T10

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.TC.Thin

structure AECoverHyp {G : Type} [Group G] {P : Set (Subgroup G)} {k : ℕ} (I : AEIdent P k) :
    Prop where
  ker_two : IsPGroup 2 ↥I.φ.ker
  card : ∀ L ∈ P, Nat.card ↥L = 8
  conj_mem : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P
  label_inj : ∀ L ∈ P, ∀ L' ∈ P,
    (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L'
  twin_comm : ∀ (α : Finset (Fin k)) (h : α.card = 4), ∀ L ∈ P, ∀ L' ∈ P,
    (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α h true →
    (L'.subgroupOf (pSpan P)).map I.φ = AE.memBar α h false →
    ∀ x ∈ L, ∀ y ∈ L', x * y = y * x
  twin_z : ∀ (α : Finset (Fin k)) (h : α.card = 4), ∀ L ∈ P, ∀ L' ∈ P,
    (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α h true →
    (L'.subgroupOf (pSpan P)).map I.φ = AE.memBar α h false →
    ∀ u u' : G, IsUniqueInvolution L u → IsUniqueInvolution L' u' → u = u'

@[expose] def AECoverElemO2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Set (Subgroup G)) (k : ℕ) (I : AEIdent P k),
    5 ≤ k → AECoverHyp I →
      ∀ T : Subgroup ↥(pSpan P), T.Normal → IsPGroup 2 ↥T →
        ∀ a ∈ T, ∀ b ∈ T, a * b = b * a ∧ a * a = 1

@[expose] def AECoverOddKer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Set (Subgroup G)) (k : ℕ) (I : AEIdent P k),
    5 ≤ k → Odd k → AECoverHyp I → I.φ.ker = ⊥

end CFSG.ClassicalInvolution.Q3.TL4
