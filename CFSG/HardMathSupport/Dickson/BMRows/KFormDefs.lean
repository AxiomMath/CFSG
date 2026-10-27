module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporRows

public section

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Blueprint
open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def I1416QSporSK : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (s : TauCeti.SporadicName),
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    (s = .B → CFSG.Open.IsKGroup (NativeSporadic.Carrier .B)) →
    (s = .M → CFSG.Open.IsKGroup (NativeSporadic.Carrier .M)) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ β : MulAut S, β ^ p = 1 → β ≠ 1 → ∀ J : Subgroup S,
      GLAPComponent p (fixSubgroup β) J → ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p →
      IsChevSimple q (PSimple p J) →
      (∃ A : Subgroup (MulAut (PSimple p J)), IsElemAbelian p A ∧ p ^ 2 ≤ Nat.card A) → False

@[expose] def I1416TwoSporSK : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (s : TauCeti.SporadicName),
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    (s = .B → CFSG.Open.IsKGroup (NativeSporadic.Carrier .B)) →
    (s = .M → CFSG.Open.IsKGroup (NativeSporadic.Carrier .M)) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ β : MulAut S, β ^ p = 1 → β ≠ 1 → ∀ K : Subgroup S,
      GLAPComponent p (fixSubgroup β) K → IsChevSimple 2 (PSimple p K) →
      p ^ 2 ∣ Nat.card (MulAut (PSimple p K)) →
      ¬ (p = 3 ∧ CFSG.HardMathSupport.Timmesfeld.ComponentBalance.IsL2TwoPowOdd (PSimple p K)) →
      p = 3 ∧ catalogIs (PSimple 3 K) (fun i => S10.isA6 i ∨ isA8 i ∨ isG2der i ∨ S9.isU4two i)

@[expose] def I1416Chev2SporListK : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (s : TauCeti.SporadicName),
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    (s = .B → CFSG.Open.IsKGroup (NativeSporadic.Carrier .B)) →
    (s = .M → CFSG.Open.IsKGroup (NativeSporadic.Carrier .M)) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ β : MulAut S, β ^ p = 1 → β ≠ 1 → ∀ K : Subgroup S,
      GLAPComponent p (fixSubgroup β) K → IsChevSimple 2 (PSimple p K) →
      catalogIs (PSimple p K) chev2Spor

theorem i1416QSporSK_iff : I1416QSporSK ↔ ∀ (s : TauCeti.SporadicName) (p : ℕ),
    (s = .B → CFSG.Open.IsKGroup (NativeSporadic.Carrier .B)) →
    (s = .M → CFSG.Open.IsKGroup (NativeSporadic.Carrier .M)) → I1416QRows.I1416QRow s p := by
  constructor
  · intro h s p hB hM S _ _ he hp hp2 β hβ hβ1 J hJ q hq hq2 hqp hc hA
    exact h S s he hB hM p hp hp2 β hβ hβ1 J hJ q hq hq2 hqp hc hA
  · intro h S _ _ s he hB hM p hp hp2 β hβ hβ1 J hJ q hq hq2 hqp hc hA
    exact h s p hB hM S he hp hp2 β hβ hβ1 J hJ q hq hq2 hqp hc hA

theorem i1416TwoSporSK_iff : I1416TwoSporSK ↔ ∀ (s : TauCeti.SporadicName) (p : ℕ),
    (s = .B → CFSG.Open.IsKGroup (NativeSporadic.Carrier .B)) →
    (s = .M → CFSG.Open.IsKGroup (NativeSporadic.Carrier .M)) → I1416Rows.I1416SporRow s p := by
  constructor
  · intro h s p hB hM S _ _ he hp hp2 β hβ hβ1 K hK hc ha hl
    obtain ⟨h3, h'⟩ := h S s he hB hM p hp hp2 β hβ hβ1 K hK hc ha hl
    subst h3
    exact ⟨rfl, h'⟩
  · intro h S _ _ s he hB hM p hp hp2 β hβ hβ1 K hK hc ha hl
    obtain ⟨h3, h'⟩ := h s p hB hM S he hp hp2 β hβ hβ1 K hK hc ha hl
    subst h3
    exact ⟨rfl, h'⟩

theorem i1416Chev2SporListK_iff : I1416Chev2SporListK ↔ ∀ (s : TauCeti.SporadicName) (p : ℕ),
    (s = .B → CFSG.Open.IsKGroup (NativeSporadic.Carrier .B)) →
    (s = .M → CFSG.Open.IsKGroup (NativeSporadic.Carrier .M)) → Chev2Rows.CRow s p := by
  constructor
  · intro h s p hB hM S _ _ he hp hp2 β hβ hβ1 J hJ hc
    exact h S s he hB hM p hp hp2 β hβ hβ1 J hJ hc
  · intro h S _ _ s he hB hM p hp hp2 β hβ hβ1 J hJ hc
    exact h s p hB hM S he hp hp2 β hβ hβ1 J hJ hc

end CFSG.HardMathSupport.Dickson.BMRows
