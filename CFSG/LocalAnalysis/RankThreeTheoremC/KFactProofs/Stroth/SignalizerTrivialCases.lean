module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial

open CFSG.Open
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open scoped MatrixGroups

@[expose] def SignalizerTrivialOn (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  ∀ P : Sylow p K, ∀ W : Subgroup (MulAut K), Nat.Coprime p (Nat.card W) →
    (∀ g ∈ (P : Subgroup K), ∀ w ∈ W, MulAut.conj g * w * (MulAut.conj g)⁻¹ ∈ W) → W = ⊥

@[expose] def SignalizerTrivialL2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (K : Type) [Group K] [Finite K],
    Nonempty (K ≃* PSL(2, GaloisField p 2)) → SignalizerTrivialOn p K

@[expose] def SignalizerTrivialU3 : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (K : Type) [Group K] [Finite K],
    (∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ IsoLie K (.twistedA 2 q)) →
    SignalizerTrivialOn p K

@[expose] def SignalizerTrivialAlt : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (K : Type) [Group K] [Finite K],
    Nonempty (K ≃* alternatingGroup (Fin (2 * p))) → SignalizerTrivialOn p K

@[expose] def SignalizerTrivialTits : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsoLie K .tits → SignalizerTrivialOn 5 K

@[expose] def SignalizerTrivialMcL : Prop :=
  ∀ (K : Type) [Group K] [Finite K],
    Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.McL).Group) →
    SignalizerTrivialOn 5 K

@[expose] def SignalizerTrivialJ4 : Prop :=
  ∀ (K : Type) [Group K] [Finite K],
    Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J4).Group) →
    SignalizerTrivialOn 11 K

theorem kFactSignalizerTrivial_of_cases (hL2 : SignalizerTrivialL2) (hU3 : SignalizerTrivialU3)
    (hAlt : SignalizerTrivialAlt) (hTits : SignalizerTrivialTits) (hMcL : SignalizerTrivialMcL)
    (hJ4 : SignalizerTrivialJ4) : KFactSignalizerTrivial := by
  intro p hp hp5 K _ _ _ _ _ hlist hFi P W hW hnorm
  have hcop : Nat.Coprime p (Nat.card W) := hW
  rcases hlist with ⟨hf, he⟩ | hU | ⟨-, he⟩ | ⟨rfl, -⟩ | ⟨rfl, hT | hM | hF⟩ | ⟨rfl, hJ⟩
  · exact hL2 p hp5 K he P W hcop hnorm
  · exact hU3 p hp hp5 K hU P W hcop hnorm
  · exact hAlt p hp hp5 K he P W hcop hnorm
  · omega
  · exact hTits K hT P W hcop hnorm
  · exact hMcL K hM P W hcop hnorm
  · exact absurd hF hFi
  · exact hJ4 K hJ P W hcop hnorm

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial
