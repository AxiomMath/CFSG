module

public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.Adapters.LinearCatalogStated
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3

open TauCeti

theorem card_eq_three_pow {q : PrimePower} (hp : q.p = 3) : q.card = 3 ^ q.exponent := by
  rw [PrimePower.card_def, hp]

section Classical

theorem rank_dichotomy_classical {G : Type} [Group G] [Finite G] (d : ValidLieTypeIndex)
    (hd : d.1.characteristic = 3)
    (hcl : (∃ r q, d.1 = .A r q) ∨ (∃ r q, d.1 = .twistedA r q) ∨ (∃ r q, d.1 = .B r q) ∨
      (∃ r q, d.1 = .C r q) ∨ (∃ r q, d.1 = .D r q) ∨ (∃ r q, d.1 = .twistedD r q))
    (e : G ≃* (CFSGIndex.lie d).Group) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) ∨
      (∃ q, d.1 = .A 1 q ∧ q.card = 27 ∧ 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G)) ∨
      (∃ q, d.1 = .A 2 q ∧ q.card = 3) ∨ (∃ q, d.1 = .twistedA 2 q ∧ q.card = 3) := by
  obtain ⟨dd, hv⟩ := d
  have hr := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hdup := ((LieTypeIndex.valid_iff _).1 hv).2
  simp only [LieTypeIndex.isDuplicateRepresentative_iff] at hdup
  cases dd with
  | A r q =>
    have hp : q.p = 3 := by simpa using hd
    have hm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    have hrk := CFSG.SectionRank.classical_model_rank (by omega) hm
    rw [hp] at hrk
    have hc := card_eq_three_pow hp
    rcases hrk.2.2 with ⟨-, (⟨hn, hf⟩ | ⟨hn, hf⟩ | h4)⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | h4
    ·
      have hr1 : r = 1 := by omega
      subst hr1
      by_cases hf4 : 4 ≤ q.exponent
      · exact Or.inl (le_trans hf4 hf)
      · right
        left
        refine ⟨q, rfl, ?_, ?_⟩
        · have h1 := hr.2 rfl
          simp only [PrimePower.card_def, hp] at h1
          have h9 : ¬ (3 : ℕ) ^ q.exponent = 9 := fun h =>
            hdup (Or.inl ⟨rfl, Or.inr (Or.inr (by simpa [PrimePower.card_def, hp] using h))⟩)
          have : q.exponent = 3 := by
            have := q.exponent_pos
            interval_cases (q.exponent) <;> simp_all
          rw [hc, this]
          norm_num
        · have h1 := hr.2 rfl
          simp only [PrimePower.card_def, hp] at h1
          have h9 : ¬ (3 : ℕ) ^ q.exponent = 9 := fun h =>
            hdup (Or.inl ⟨rfl, Or.inr (Or.inr (by simpa [PrimePower.card_def, hp] using h))⟩)
          have : q.exponent = 3 := by
            have := q.exponent_pos
            interval_cases (q.exponent) <;> simp_all
          rw [this] at hf
          exact hf
    ·
      have hr2 : r = 2 := by omega
      subst hr2
      by_cases hf2 : 2 ≤ q.exponent
      · exact Or.inl (by omega)
      · right
        right
        left
        refine ⟨q, rfl, ?_⟩
        have : q.exponent = 1 := by
          have := q.exponent_pos
          omega
        rw [hc, this]
        norm_num
    · exact Or.inl h4
    · cases ht
    · cases ht
    · exact Or.inl h4
  | twistedA r q =>
    have hp : q.p = 3 := by simpa using hd
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    have hrk := CFSG.SectionRank.classical_model_rank (by omega) hm
    rw [hp] at hrk
    have hc := card_eq_three_pow hp
    rcases hrk.2.2 with ⟨ht, -⟩ | ⟨-, (⟨hn, hf⟩ | h4)⟩ | ⟨ht, -⟩ | h4
    · cases ht
    · have hr2 : r = 2 := by omega
      subst hr2
      by_cases hf2 : 2 ≤ q.exponent
      · exact Or.inl (by omega)
      · right
        right
        right
        refine ⟨q, rfl, ?_⟩
        have : q.exponent = 1 := by
          have := q.exponent_pos
          omega
        rw [hc, this]
        norm_num
    · exact Or.inl h4
    · cases ht
    · exact Or.inl h4
  | B r q =>
    have hp : q.p = 3 := by simpa using hd
    have hc := card_eq_three_pow hp
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      have hrk := CFSG.SectionRank.classical_model_rank (by omega) hm
      rw [hp] at hrk
      rcases hrk.2.2 with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨-, (⟨-, hf⟩ | h4)⟩ | h4
      · cases ht
      · cases ht
      · left
        have h3 : q.card ≠ 3 := fun h => hdup ⟨rfl, h⟩
        have hf2 : 2 ≤ q.exponent := by
          have := q.exponent_pos
          by_contra hlt
          have h1 : q.exponent = 1 := by omega
          apply h3
          rw [hc, h1]
          norm_num
        omega
      · exact Or.inl h4
      · exact Or.inl h4
    · have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv (by omega)
        hr3 e
      have hrk := CFSG.SectionRank.classical_model_rank (by omega) hm
      rw [hp] at hrk
      rcases hrk.2.2 with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | h4
      · cases ht
      · cases ht
      · cases ht
      · exact Or.inl h4
  | C r q =>
    have hp : q.p = 3 := by simpa using hd
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e
    have hrk := CFSG.SectionRank.classical_model_rank (by omega) hm
    rw [hp] at hrk
    rcases hrk.2.2 with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨-, (⟨hn, -⟩ | h4)⟩ | h4
    · cases ht
    · cases ht
    · omega
    · exact Or.inl h4
    · exact Or.inl h4
  | D r q =>
    have hp : q.p = 3 := by simpa using hd
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e
    have hrk := CFSG.SectionRank.classical_model_rank (by omega) hm
    rw [hp] at hrk
    rcases hrk.2.2 with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | h4
    · cases ht
    · cases ht
    · cases ht
    · exact Or.inl h4
  | twistedD r q =>
    have hp : q.p = 3 := by simpa using hd
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e
    have hrk := CFSG.SectionRank.classical_model_rank (by omega) hm
    rw [hp] at hrk
    rcases hrk.2.2 with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | h4
    · cases ht
    · cases ht
    · cases ht
    · exact Or.inl h4
  | E6 q => simp at hcl
  | E7 q => simp at hcl
  | E8 q => simp at hcl
  | F4 q => simp at hcl
  | G2 q => simp at hcl
  | twistedE6 q => simp at hcl
  | trialityD4 q => simp at hcl
  | suzuki m => simp at hcl
  | reeG2 m => simp at hcl
  | reeF4 m => simp at hcl
  | tits => simp at hcl

end Classical

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3
