module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsUniOdd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsTwADefs
public import CFSG.LieType.SeitzGeneration.SeitzStatus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel


theorem compNormal_twistedA_of_not_dvd {p : ℕ} {T : Type} [Group T] [Finite T]
    {d : TauCeti.ValidLieTypeIndex} (hd : OddLie p T d) (hQ : PlaneIdxTwA d.1)
    (hnd : ¬ TwADvd p d.1) (x : MulAut T) (hxp : x ^ p = 1) : CompNormal x := by
  obtain ⟨e⟩ := hd.iso
  obtain ⟨d, hv⟩ := d
  cases d with
  | twistedA r q =>
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    obtain ⟨⟨hℓ, hf, hn3, hq⟩, K, _, _, hK, ⟨eT⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := r + 1) (K := K))
    let e' : T ≃* primeFormP h (idGram K (r + 1)) :=
      (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
    have hpq : p ≠ q.p := by
      have h1 : (TauCeti.LieTypeIndex.twistedA r q).characteristic = q.p :=
        TauCeti.LieTypeIndex.characteristic_twistedA r q
      exact h1 ▸ hd.ne
    have hpQ : ¬ p ∣ q.p ^ q.exponent + 1 := fun hdvd =>
      hnd ⟨r, q, rfl, by rwa [TauCeti.PrimePower.card_def]⟩
    refine CompNormal.of_congr e' ?_
    exact compNormal_primeFormP_of_not_dvd h hn3 (fun h3 => hq (Prod.ext h3.1 h3.2)) hd.prime hd.odd
      hpq hpQ _ (by rw [← map_pow, hxp, map_one])
  | _ => exact absurd hQ (by simp [PlaneIdxTwA])

theorem genPlaneTwANotDvd_holds : GenPlaneTwANotDvd := by
  intro p T _ _ d hd hQ hnd P hP hcard J
  obtain ⟨e⟩ := hd.iso
  haveI := (CFSG.Assembly.lie_finite_simple d).2
  exact not_forall_glaPComponent_of_compNormal CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
    (genCompQuasiOn_holds' PlaneIdxTwA) hd hQ e.isSimpleGroup hP hcard
    (fun x hx _ => compNormal_twistedA_of_not_dvd hd hQ hnd x (hP.2 x hx)) J

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen

end
