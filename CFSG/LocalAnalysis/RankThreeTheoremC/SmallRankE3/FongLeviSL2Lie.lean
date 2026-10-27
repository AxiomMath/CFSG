module

public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K136Parab

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open TauCeti

noncomputable def sl2MulEquivOfRingEquiv {R S : Type} [CommRing R] [CommRing S] (f : R ≃+* S) :
    Matrix.SpecialLinearGroup (Fin 2) R ≃* Matrix.SpecialLinearGroup (Fin 2) S :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map (f : R →+* S))
    (Matrix.SpecialLinearGroup.map (f.symm : S →+* R))
    (by ext A i j; simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply])
    (by ext A i j; simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply])

theorem nonempty_sl2_mulEquiv_lie {F : Type} [Field F] [Finite F] {q : PrimePower}
    (hq2 : q.p = 2) (hv : (LieTypeIndex.A 1 q).Valid) (hF : Nat.card F = q.p ^ q.exponent) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ≃* ValidLieTypeIndex.Group ⟨.A 1 q, hv⟩) := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hchar : ringChar (GaloisField q.p q.exponent) = 2 :=
    (ringChar.eq (GaloisField q.p q.exponent) q.p).trans hq2
  haveI : CharP (GaloisField q.p q.exponent) 2 := ringChar.of_eq hchar
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card q.p q.exponent q.exponent_pos.ne'
  obtain ⟨σ⟩ : Nonempty (F ≃+* GaloisField q.p q.exponent) := by
    haveI := Fintype.ofFinite F
    haveI := Fintype.ofFinite (GaloisField q.p q.exponent)
    refine ⟨FiniteField.ringEquivOfCardEq ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, hcard]
  exact ⟨(sl2MulEquivOfRingEquiv σ).trans
    (((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv).trans
      ((QuotientGroup.quotientMulEquivOfEq
        (Parrott.P614.P614K136.center_SL2_eq_bot (F := GaloisField q.p q.exponent))).trans
        QuotientGroup.quotientBot)).symm)⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
