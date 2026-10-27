module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCase
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.PartOne.Census3.Interface

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped MatrixGroups

@[expose] def IsRankTwoSEGroup (p : ℕ) (K : Type) [Group K] : Prop :=
  (∃ _ : Fact p.Prime, Nonempty (K ≃* PSL(2, GaloisField p 2))) ∨
  (∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ IsoLie K (.twistedA 2 q)) ∨
  (5 ≤ p ∧ Nonempty (K ≃* alternatingGroup (Fin (2 * p)))) ∨
  (p = 3 ∧ ((∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ IsoLie K (.A 2 q)) ∨
    Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M11).Group))) ∨
  (p = 5 ∧ (IsoLie K .tits ∨
    Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.McL).Group) ∨
    Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group))) ∨
  (p = 11 ∧ Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J4).Group))

theorem isoLie_of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    {d : TauCeti.LieTypeIndex} (h : IsoLie K d) : IsoLie K' d := by
  obtain ⟨hv, ⟨f⟩⟩ := h
  exact ⟨hv, ⟨e.symm.trans f⟩⟩

theorem IsRankTwoSEGroup.of_mulEquiv {p : ℕ} {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (h : IsRankTwoSEGroup p K) : IsRankTwoSEGroup p K' := by
  rcases h with ⟨hf, ⟨f⟩⟩ | ⟨q, hq1, hq2, hl⟩ | ⟨h5, ⟨f⟩⟩ | ⟨h3, h⟩ | ⟨h5, h⟩ | ⟨h11, ⟨f⟩⟩
  · exact Or.inl ⟨hf, ⟨e.symm.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨q, hq1, hq2, isoLie_of_mulEquiv e hl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h5, ⟨e.symm.trans f⟩⟩))
  · rcases h with ⟨q, hq1, hq2, hl⟩ | f
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, Or.inl ⟨q, hq1, hq2, isoLie_of_mulEquiv e hl⟩⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, Or.inr ⟨e.symm.trans f.some⟩⟩)))
  · rcases h with hl | f | f
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h5, Or.inl (isoLie_of_mulEquiv e hl)⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h5, Or.inr (Or.inl ⟨e.symm.trans f.some⟩)⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h5, Or.inr (Or.inr ⟨e.symm.trans f.some⟩)⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h11, ⟨e.symm.trans f⟩⟩))))

@[expose] def StronglyEmbeddedCyclicOuterKFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal → IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → Subgroup.centralizer (K : Set X) = ⊥ →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Sylow p X, IsCyclic ↥((P : Subgroup X) ⊓ K) →
      2 ≤ CFSG.Open.pRank p (P : Subgroup X) → rankThreeGamma 1 p (P : Subgroup X) ≠ ⊤ →
      (p = 3 ∧ IsoLie ↥K (.A 1 ⟨2, 3, by norm_num, by norm_num⟩)) ∨ (p = 5 ∧ IsoLie ↥K (.suzuki 2))

@[expose] def KFactOutCyclic : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K, IsCyclic ↥(T : Subgroup K) →
      CFSG.Open.pRank p (⊤ : Subgroup (Outer K)) ≤ 1

@[expose] def KF1On (Y : Type) [Group Y] [Finite Y] : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ L : Subgroup Y, CFSG.Open.IsQuasisimple L →
    IsCatalogGroup (L ⧸ Subgroup.center L) → IsPGroup p (Subgroup.center L) →
      p ∣ Nat.card (Subgroup.center L) → 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup L)

@[expose] def GenericAt (G : Type) [Group G] [Finite G]
    (Φ : ∀ p : ℕ, Sylow p G → Subgroup G → G → Prop) : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G), IsCoreMaxLocal p P M →
    ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M → LargerPrimesUnique G p →
      ∀ x : G, IsGenericPoint p P M x → Φ p P M x

@[expose] def GL83GenericPrimeThree (G : Type) [Group G] [Finite G] : Prop :=
  GenericAt G fun p _ _ _ => p ≠ 3

end CFSG.LocalAnalysis.RankThreeTheoremC
