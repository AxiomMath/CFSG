module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.AGLEmbedding.GenericTargetFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

theorem isSimpleGroup_of_isCaseTwoGroup_three {L : Type} [Group L] (hL : IsCaseTwoGroup 3 L) :
    IsSimpleGroup L := by
  obtain ⟨d, hd, ⟨e⟩⟩ := hL
  rcases hd with ⟨-, q, hqp, hqe, hdq⟩ | ⟨h35, -⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨eP⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := 2) (n := 3) (d := d)
      ⟨q, hdq, hqp, hqe⟩
    have hcard : Nat.card (GaloisField 2 3) = 8 := by
      rw [GaloisField.card 2 3 (by norm_num)]
      norm_num
    have : IsSimpleGroup (PSL2GF 2 3) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hcard]; norm_num)
    exact (e.trans eP).isSimpleGroup
  · omega

section Defs

variable {G : Type} [Group G]

@[expose] def BlockL28Hyps (M S L : Subgroup G) : Prop :=
  Open.IsKGroup ↥M ∧ Asc81bHyp M S ∧ IsWeakSBlock M S L ∧ NineThreeConclusion M S L ∧
    ¬ InClassXBlock L ∧ ¬ IsSylowTwoOf (S ⊓ L) L

@[expose] def HasL28Quot (S L : Subgroup G) : Prop :=
  ∃ T : Subgroup G, T ≤ Subgroup.normalizer (S : Set G) ⊓ L ∧
    Subgroup.normalizer (S : Set G) ⊓ L ≤ Subgroup.normalizer (T : Set G) ∧
    ∃ (d : TauCeti.ValidLieTypeIndex) (ψ : T →* CatGroup d), IsCaseTwoIndex 3 d ∧
      Function.Surjective ψ

@[expose] def HasL28Quot2 (S L : Subgroup G) : Prop :=
  ∃ T : Subgroup G, T ≤ Subgroup.normalizer (S : Set G) ⊓ L ∧
    Subgroup.normalizer (S : Set G) ⊓ L ≤ Subgroup.normalizer (T : Set G) ∧
    ∃ (d₁ d₂ : TauCeti.ValidLieTypeIndex) (ψ : T →* CatGroup d₁ × CatGroup d₂),
      IsCaseTwoIndex 3 d₁ ∧ IsCaseTwoIndex 3 d₂ ∧ Function.Surjective ψ

@[expose] def KFactBlockL28Transvection : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), BlockL28Hyps M S L →
    NineThreeThree M S L → ¬ HasL28Quot S L

@[expose] def KFactBlockL28Rank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), BlockL28Hyps M S L →
    NineThreeTwo M S L → HasL28Quot S L →
    ∃ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ barM M L ∧ IsElemAbelian 7 E ∧
      Nat.card E = 7 ^ 2 ∧
      E ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥

@[expose] def KFactBlockL28TwoRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), BlockL28Hyps M S L →
    NineThreeTwo M S L → HasL28Quot2 S L → 3 ≤ Open.pRank 7 (barM M L)

end Defs

end CFSG.LocalAnalysis.RankThreeTheoremC
