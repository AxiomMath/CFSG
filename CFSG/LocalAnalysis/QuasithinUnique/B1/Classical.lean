module

public import CFSG.LocalAnalysis.QuasithinUnique.B1.Interface
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.QuasithinUnique.B1

open TauCeti CFSG.Assembly.LowTwoRank

theorem catalogBridgeFor_A (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid) :
    CatalogBridgeFor (.lie ⟨.A r q, hv⟩) := by
  intro G _ _ _ ⟨e⟩
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
  exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, hm⟩))

theorem catalogBridgeFor_C (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.C r q).Valid) :
    CatalogBridgeFor (.lie ⟨.C r q, hv⟩) := by
  intro G _ _ _ ⟨e⟩
  exact CFSG.QuasithinUnique.SQTK.blueprintCatalog_of_typeC r q hv e

theorem catalogBridgeFor_B2 (q : PrimePower) (hv : (LieTypeIndex.B 2 q).Valid) :
    CatalogBridgeFor (.lie ⟨.B 2 q, hv⟩) := by
  intro G _ _ _ ⟨e⟩
  exact CFSG.QuasithinUnique.SQTK.blueprintCatalog_of_typeB2 q hv e

theorem catalogBridgeFor_twistedA (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) :
    CatalogBridgeFor (.lie ⟨.twistedA r q, hv⟩) := by
  intro G _ _ _ ⟨e⟩
  exact CFSG.QuasithinUnique.SQTK.blueprintCatalog_of_twistedA r q hv e

end CFSG.QuasithinUnique.B1
