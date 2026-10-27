module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerNoncentral2_7KFact

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TwoSignalizer

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open scoped MatrixGroups

@[expose] def TwoSignalizerOn (p : ℕ) (C : ∀ (X : Type) [Group X], Subgroup X → Subgroup X → Prop) :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal → IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) →
    ∀ B : Subgroup X, IsElemAbelian p B → Nat.card B = p ^ 2 → B ⊓ centralizer (K : Set X) = ⊥ →
      C X K B → ∀ T : Subgroup X, IsPGroup 2 T → B ≤ normalizer (T : Set X) →
        ⁅B, T⁆ ≤ centralizer (K : Set X)

@[expose] def TwoSignalizerL2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
    TwoSignalizerOn p fun _ _ K B => Nonempty (↥K ≃* PSL(2, GaloisField p 2)) ∧ B ≤ K

@[expose] def TwoSignalizerU3 : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 →
    TwoSignalizerOn p fun _ _ K B =>
      (∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ IsoLie ↥K (.twistedA 2 q)) ∧ B ≤ K

@[expose] def TwoSignalizerAlt : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p →
    TwoSignalizerOn p fun _ _ K B => Nonempty (↥K ≃* alternatingGroup (Fin (2 * p))) ∧ B ≤ K

@[expose] def TwoSignalizerL34 : Prop :=
  TwoSignalizerOn 3 fun _ _ K B =>
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ IsoLie ↥K (.A 2 q)) ∧ B ≤ K

@[expose] def TwoSignalizerM11 : Prop :=
  TwoSignalizerOn 3 fun _ _ K B =>
    Nonempty (↥K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M11).Group) ∧ B ≤ K

@[expose] def TwoSignalizerFive : Prop :=
  TwoSignalizerOn 5 fun _ _ K B =>
    (IsoLie ↥K .tits ∨
      Nonempty (↥K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.McL).Group) ∨
      Nonempty (↥K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group)) ∧ B ≤ K

@[expose] def TwoSignalizerJ4 : Prop :=
  TwoSignalizerOn 11 fun _ _ K B =>
    Nonempty (↥K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J4).Group) ∧ B ≤ K

@[expose] def TwoSignalizerL28 : Prop :=
  TwoSignalizerOn 3 fun _ _ K _ => IsoLie ↥K (.A 1 ⟨2, 3, by norm_num, by norm_num⟩)

@[expose] def TwoSignalizerSz32 : Prop :=
  TwoSignalizerOn 5 fun _ _ K _ => IsoLie ↥K (.suzuki 2)

theorem signalizerTwoGroupKFact_of_cases (hL2 : TwoSignalizerL2) (hU3 : TwoSignalizerU3)
    (hAlt : TwoSignalizerAlt) (hL34 : TwoSignalizerL34) (hM11 : TwoSignalizerM11)
    (hFive : TwoSignalizerFive) (hJ4 : TwoSignalizerJ4) (hL28 : TwoSignalizerL28)
    (hSz : TwoSignalizerSz32) : SignalizerTwoGroupKFact := by
  intro X _ _ K hKn hs hnab _hcat p hp hp2 B hB hBc hBC hcase T hT hBT
  rcases hcase with ⟨hlist, hBK⟩ | ⟨rfl, hL⟩ | ⟨rfl, hS⟩
  · rcases hlist with ⟨hf, he⟩ | hU | ⟨hp5, he⟩ | ⟨rfl, h3 | h3⟩ | ⟨rfl, h5⟩ | ⟨rfl, hJ⟩
    · exact hL2 p hp2 X K hKn hs hnab B hB hBc hBC ⟨he, hBK⟩ T hT hBT
    · exact hU3 p hp hp2 X K hKn hs hnab B hB hBc hBC ⟨hU, hBK⟩ T hT hBT
    · exact hAlt p hp hp5 X K hKn hs hnab B hB hBc hBC ⟨he, hBK⟩ T hT hBT
    · exact hL34 X K hKn hs hnab B hB hBc hBC ⟨h3, hBK⟩ T hT hBT
    · exact hM11 X K hKn hs hnab B hB hBc hBC ⟨h3, hBK⟩ T hT hBT
    · exact hFive X K hKn hs hnab B hB hBc hBC ⟨h5, hBK⟩ T hT hBT
    · exact hJ4 X K hKn hs hnab B hB hBc hBC ⟨hJ, hBK⟩ T hT hBT
  · exact hL28 X K hKn hs hnab B hB hBc hBC hL T hT hBT
  · exact hSz X K hKn hs hnab B hB hBc hBC hS T hT hBT

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TwoSignalizer
