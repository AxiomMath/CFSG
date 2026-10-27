module

public import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.Open.StatedAPI

open CFSG.Assembly.LowTwoRank TauCeti

theorem statedClassicalModel_of_mulEquiv_typeA {X : Type} [Group X] {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.A r q).Valid) (e : X ≃* ValidLieTypeIndex.Group ⟨.A r q, hv⟩) :
    StatedClassicalModel X .PSL (r + 1) q.p q.exponent := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have h4 : r = 1 → 4 ≤ q.p ^ q.exponent := fun h => by
    simpa [PrimePower.card_def] using hrange.2 h
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

end CFSG.Open.StatedAPI
