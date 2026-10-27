module

public import CFSG.Adapters.LinearCatalog
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Curtis.Coordinator.SPLCellMult
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneHilbertNinety

public section

open CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Curtis.Coordinator

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.LocalAnalysis.ComponentInitial

theorem statedClassicalModel_typeA' {K : Type} [Group K] {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A r q).Valid)
    (e : K ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A r q, hv⟩) :
    StatedClassicalModel K .PSL (r + 1) q.p q.exponent := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have h4 : r = 1 → 4 ≤ q.p ^ q.exponent := fun h => by
    simpa [TauCeti.PrimePower.card_def] using hrange.2 h
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

end CFSG.HardMathSupport.Curtis.UnitaryLevi
