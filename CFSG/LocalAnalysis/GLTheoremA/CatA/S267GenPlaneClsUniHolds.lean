module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsUni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsTwADefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

theorem genPlaneTwADvd_holds : GenPlaneTwADvd := by
  intro p T _ _ d hd hdvd
  obtain ⟨e⟩ := hd.iso
  obtain ⟨r, q, hdq, hpq⟩ := hdvd
  obtain ⟨d, hv⟩ := d
  change d = .twistedA r q at hdq
  subst hdq
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨⟨hℓ, hf, hn3, -⟩, K, _, _, hK, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := r + 1) (K := K))
  let e' : T ≃* primeFormP h (idGram K (r + 1)) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have hchar : (TauCeti.LieTypeIndex.twistedA r q).characteristic = q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA r q
  have hpq' : p ≠ q.p := hchar ▸ hd.ne
  have hℓ2 : q.p ≠ 2 := hchar ▸ hd.charOdd
  exact PlaneNoComp.of_mulEquiv hd.prime e'
    (planeNoComp_primeFormP_of_dvd h hn3 hd.prime hd.odd hpq' hℓ2
      (by rwa [TauCeti.PrimePower.card_def] at hpq))

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
