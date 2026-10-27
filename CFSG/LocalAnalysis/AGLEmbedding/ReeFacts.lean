module

public import CFSG.LocalAnalysis.AGLEmbedding.GenericTargetFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

theorem IsReeGTwoIndex.exists_eq {p : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (h : IsReeGTwoIndex p d) :
    p = 3 ∧ ∃ m : ℕ, 1 ≤ m ∧ d.1 = .reeG2 m ∧ d.1.fieldExponent = 2 * m + 1 := by
  obtain ⟨hp, m, hm⟩ := h
  refine ⟨hp, m, ?_, hm, by rw [hm, TauCeti.LieTypeIndex.fieldExponent_reeG2]⟩
  have hv := ((TauCeti.LieTypeIndex.valid_iff _).mp d.2).1
  rw [hm] at hv
  simpa using hv

theorem IsReeGTwoIndex.odd_fieldExponent {p : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (h : IsReeGTwoIndex p d) : Odd d.1.fieldExponent := by
  obtain ⟨-, m, -, -, he⟩ := h.exists_eq
  exact ⟨m, he⟩

theorem IsReeGTwoIndex.three_le_fieldExponent {p : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (h : IsReeGTwoIndex p d) : 3 ≤ d.1.fieldExponent := by
  obtain ⟨-, m, hm, -, he⟩ := h.exists_eq
  omega

@[expose] def KFactReeSchur : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex), IsReeGTwoIndex 3 d →
    Open.IsQuasisimple K → IsPGroup 3 (Subgroup.center K) →
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    Subgroup.center K = ⊥

@[expose] def KFactReeSylowCenterTorus : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex), IsReeGTwoIndex 3 d →
    Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → ∀ U : Sylow 3 L,
    ∃ ψ : Multiplicative (GaloisField 3 d.1.fieldExponent) →* L, Function.Injective ψ ∧
      ψ.range = (U : Subgroup L) ⊓ Subgroup.centralizer ((U : Subgroup L) : Set L) ∧
      ∀ μ : (GaloisField 3 d.1.fieldExponent)ˣ,
        ∃ c ∈ Subgroup.normalizer ((U : Subgroup L) : Set L),
        ∀ a : Multiplicative (GaloisField 3 d.1.fieldExponent),
          c * ψ a * c⁻¹ = ψ (Multiplicative.ofAdd ((μ : GaloisField 3 d.1.fieldExponent) *
            Multiplicative.toAdd a))

@[expose] def KFactReeCenterCentralizer : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex), IsReeGTwoIndex 3 d →
    Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → ∀ (U : Sylow 3 L) (α : MulAut L),
    (∀ z ∈ (U : Subgroup L) ⊓ Subgroup.centralizer ((U : Subgroup L) : Set L), α z = z) →
    ∃ u ∈ (U : Subgroup L), α = MulAut.conj u

@[expose] def KFactReeBorelMaximal : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex), IsReeGTwoIndex 3 d →
    Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → ∀ U : Sylow 3 L,
    IsCoatom (Subgroup.normalizer ((U : Subgroup L) : Set L))

@[expose] def KFactReeSylowNormalizerSolvable : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex), IsReeGTwoIndex 3 d →
    Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ (U : Sylow 3 L) (A : Subgroup (MulAut L)),
    (∀ α ∈ A, (U : Subgroup L).map (α : L ≃* L).toMonoidHom = U) → Group.IsSolvable A

@[expose] def KFactReeAutElemRank : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex), IsReeGTwoIndex 3 d →
    Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → ∀ E : Subgroup (MulAut L),
    IsElemAbelian 3 E → Nat.card E ≤ 3 ^ (2 * d.1.fieldExponent)

@[expose] def KFactReeAutPCard : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex), IsReeGTwoIndex 3 d →
    Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → ∀ S : Subgroup (MulAut L),
    IsPGroup 3 S → Nat.card S ∣ 3 ^ (3 * d.1.fieldExponent) * d.1.fieldExponent

@[expose] def KFactReeOrder : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex), IsReeGTwoIndex 3 d →
    Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) →
    Nat.card L = (3 ^ d.1.fieldExponent) ^ 3 * ((3 ^ d.1.fieldExponent) ^ 3 + 1) *
      (3 ^ d.1.fieldExponent - 1)

open CFSG.ComponentClassification.OuterAutomorphisms in
@[expose] def KFactReeOuterSolvable : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex), IsReeGTwoIndex 3 d →
    Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → Group.IsSolvable (Outer L)

@[expose] def KFactJStarElimReeLie : Prop :=
  ∀ d₀ : TauCeti.ValidLieTypeIndex, IsReeGTwoIndex 3 d₀ → ∀ (L : Type) [Group L] [Finite L],
    IsSimpleGroup L → ∀ d : TauCeti.ValidLieTypeIndex, P1ThreeLieList 3 d →
    ¬ IsReeGTwoIndex 3 d → Nonempty (L ≃* CatGroup d) →
    ¬ JStarElimDataOf L 3 (3 ^ (3 * d₀.1.fieldExponent) * d₀.1.fieldExponent) (CatGroup d₀)

@[expose] def KFactJStarElimReeAlt : Prop :=
  ∀ d₀ : TauCeti.ValidLieTypeIndex, IsReeGTwoIndex 3 d₀ → ∀ (L : Type) [Group L] [Finite L],
    Nonempty (L ≃* alternatingGroup (Fin (3 * 3))) →
    ¬ JStarElimDataOf L 3 (3 ^ (3 * d₀.1.fieldExponent) * d₀.1.fieldExponent) (CatGroup d₀)

@[expose] def KFactJStarElimReeSpor : Prop :=
  ∀ d₀ : TauCeti.ValidLieTypeIndex, IsReeGTwoIndex 3 d₀ → ∀ (L : Type) [Group L] [Finite L],
    ∀ s : TauCeti.SporadicName, P1ThreeSporList 3 s →
    Nonempty (L ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ¬ JStarElimDataOf L 3 (3 ^ (3 * d₀.1.fieldExponent) * d₀.1.fieldExponent) (CatGroup d₀)

@[expose] def StmtReeBorel : Prop :=
  ∀ {Y : Type} [Group Y] [Finite Y] (Rb : Sylow 3 Y) (Y₀ K : Subgroup Y)
    (d : TauCeti.ValidLieTypeIndex), IsReeGTwoIndex 3 d → ReducedNongeneration 3 Y Rb Y₀ →
    K.Normal → Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    Subgroup.centralizer (K : Set Y) = ⊥ →
    (∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) →
      W = ⊥ ∨ ((Rb : Subgroup Y) ⊓ K) ⊓ Subgroup.centralizer (((Rb : Subgroup Y) ⊓ K : Subgroup Y)
        : Set Y) ≤ W) ∧
    Y₀ ⊓ Subgroup.centralizer ((((Rb : Subgroup Y) ⊓ K) ⊓ Subgroup.centralizer
      (((Rb : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) : Subgroup Y) : Set Y) ≤
        (Rb : Subgroup Y) ⊓ K ∧
    (∃ ψ : Multiplicative (GaloisField 3 d.1.fieldExponent) →* Y, Function.Injective ψ ∧
      ψ.range = ((Rb : Subgroup Y) ⊓ K) ⊓ Subgroup.centralizer
        (((Rb : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) ∧
      ∀ μ : (GaloisField 3 d.1.fieldExponent)ˣ, ∃ c ∈ Y₀,
        ∀ a : Multiplicative (GaloisField 3 d.1.fieldExponent),
          c * ψ a * c⁻¹ = ψ (Multiplicative.ofAdd ((μ : GaloisField 3 d.1.fieldExponent) ^ 2 *
            Multiplicative.toAdd a))) ∧
    Group.IsSolvable Y₀ ∧ Open.pRank 3 (⊤ : Subgroup Y) ≤ 2 * d.1.fieldExponent

end CFSG.AGLEmbedding
