module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Glue
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven
public import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.QuasithinUnique.SQTK

open CFSG.Open.SQTKTauCeti TauCeti CFSG.Assembly.LowTwoRank

theorem stronglyQuasithin_open {G : Type} [Group G] [Finite G] (h : StronglyQuasithin G) :
    ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup G) ≤ 2 :=
  h

theorem sqtkSimpleList_of_statedClassicalModel {G : Type} [Group G] [Finite G]
    (hSQT : StronglyQuasithin G) {t : StatedLieTag} {n p f : ℕ}
    (hm : StatedClassicalModel G t n p f) : SQTKSimpleList G := by
  have hSQT' := stronglyQuasithin_open hSQT
  have hp : p.Prime := hm.1.1
  by_cases hp2 : p = 2
  · subst hp2
    rcases CFSG.SectionRank.ClassicalEven.sqt_even_classical_restriction hSQT' hm with
        ⟨rfl, rfl, hf⟩ | ⟨rfl, rfl, hf⟩ | ⟨rfl, hn, rfl⟩ | ⟨rfl, rfl, hf⟩ | ⟨rfl, rfl, hf⟩
    · exact Or.inr (Or.inr (Or.inl ⟨f, Or.inl ⟨hf, hm⟩⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨f, Or.inr (Or.inl ⟨hf, hm⟩)⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, hm⟩))))
    · exact Or.inr (Or.inr (Or.inl ⟨f, Or.inr (Or.inr (Or.inl ⟨hf, hm⟩))⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨f, Or.inr (Or.inr (Or.inr ⟨hf, hm⟩))⟩))
  · refine Or.inr (Or.inl ⟨p, hp, hp2, ?_⟩)
    rcases CFSG.SectionRank.sqt_odd_classical_restriction hSQT' hp2 hm with
        ⟨rfl, rfl, hf⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact Or.inl ⟨f, hf, hm⟩
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr hm)

theorem tcLieCase_A (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid) :
    TCLieCase ⟨.A r q, hv⟩ := by
  intro G _ _ _ _ hSQT ⟨e⟩
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hrange := ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1)
  have hr : 1 ≤ r := hrange.1
  have h4 : r = 1 → 4 ≤ q.p ^ q.exponent := by
    simpa only [PrimePower.card_def] using hrange.2
  have hm : StatedClassicalModel G .PSL (r + 1) q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, by omega, ?_, ?_⟩, GaloisField q.p q.exponent,
      inferInstance, inferInstance, GaloisField.card q.p q.exponent q.exponent_pos.ne',
      ⟨(e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv)).trans
        (projectiveSpecialLinearGroupEquivStatedProj (r + 1) (GaloisField q.p q.exponent))⟩⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      have := h4 (by omega)
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      have := h4 (by omega)
      omega
  exact sqtkSimpleList_of_statedClassicalModel hSQT hm

theorem tcLieCase_typeA (d : ValidLieTypeIndex) (hd : IsUntwistedA d) : TCLieCase d := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q => exact tcLieCase_A r q hv
  | _ => exact hd.elim

end CFSG.QuasithinUnique.SQTK
