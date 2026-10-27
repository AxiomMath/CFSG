module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique

@[expose] def KFactCaseTwoNoTwoL28 : Prop :=
  ∀ (p : ℕ) (K : Type) [Group K] [Finite K],
    (p = 3 ∧ ∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.p = 2 ∧
      q.exponent = 3 ∧ d.1 = .A 1 q) ∧ Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) →
    ∀ t : K, orderOf t = p →
      ∀ U : Subgroup (MulAut K), IsPGroup 2 U →
        MulAut.conj t ∈ Subgroup.normalizer (U : Set (MulAut K)) → U = ⊥

@[expose] def KFactCaseTwoNoTwoSz32 : Prop :=
  ∀ (p : ℕ) (K : Type) [Group K] [Finite K],
    (p = 5 ∧ ∃ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 ∧
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) →
    ∀ t : K, orderOf t = p →
      ∀ U : Subgroup (MulAut K), IsPGroup 2 U →
        MulAut.conj t ∈ Subgroup.normalizer (U : Set (MulAut K)) → U = ⊥

theorem kFactCaseTwoNoTwo_of_halves (h28 : KFactCaseTwoNoTwoL28) (h32 : KFactCaseTwoNoTwoSz32) :
    KFactCaseTwoNoTwo := by
  intro p K _ _ hK
  obtain ⟨d, hd, he⟩ := hK
  rcases hd with ⟨hp, hq⟩ | ⟨hp, hs⟩
  · exact h28 p K ⟨hp, d, hq, he⟩
  · exact h32 p K ⟨hp, d, hs, he⟩

end CFSG.AGLEmbedding
