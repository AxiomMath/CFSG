module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.TwistedA
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Adapters.CatalogueFieldBridges

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.SQTK CFSG.Adapters.RankTwoModelTransports
open CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
open Matrix

theorem primeFormP_one_mulEquiv_twistedA {q : TauCeti.PrimePower} {K : Type} [Field K]
    (h : UnitaryFieldData q.p q.exponent K) {N : ℕ} (hN : 3 ≤ N)
    (hv : (TauCeti.LieTypeIndex.twistedA (N - 1) q).Valid) :
    Nonempty (primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) ≃*
      (TauCeti.CFSGIndex.lie ⟨.twistedA (N - 1) q, hv⟩).Group) := by
  classical
  haveI : Finite K := h.finite
  haveI : Fact q.p.Prime := ⟨h.prime⟩
  let G := (TauCeti.CFSGIndex.lie ⟨.twistedA (N - 1) q, hv⟩).Group
  have hmodel : StatedClassicalModel G .PSU N q.p q.exponent := by
    have h := statedClassicalModel_twistedA (N - 1) q hv (MulEquiv.refl G)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ N)] using h
  obtain ⟨K', hF', hK', -, ⟨eP⟩⟩ := exists_primeFormP_mulEquiv_of_statedModel hmodel
  letI : Field K' := hF'
  haveI : Finite K' := hK'.finite
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype K' := Fintype.ofFinite K'
  let e1 : primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) ≃*
      StatedProj (StatedSU N (q.p ^ q.exponent) K) :=
    (Classical.choice (nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := N)))).trans
      (unitaryPSUEquiv h (by omega))
  have hcard : Fintype.card K = Fintype.card K' := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h.card, hK'.card]
  let φ : K ≃+* K' := FiniteField.ringEquivOfCardEq hcard
  let e2 : StatedProj (StatedSU N (q.p ^ q.exponent) K) ≃*
      StatedProj (StatedSU N (q.p ^ q.exponent) K') :=
    statedProjCongr (glCongr (ι := Fin N) φ) (glCongr_statedSU φ N (q.p ^ q.exponent))
      (glCongr_statedScalars φ)
  let e3 : StatedProj (StatedSU N (q.p ^ q.exponent) K') ≃*
      primeFormP hK' ((1 : GL (Fin N) K') : Matrix (Fin N) (Fin N) K') :=
    ((Classical.choice (nonempty_primeFormP_mulEquiv hK'
      (isPrimeFormGram_one (n := N)))).trans (unitaryPSUEquiv hK' (by omega))).symm
  exact ⟨e1.trans (e2.trans (e3.trans eP.symm))⟩

end CFSG.Adapters.CatalogueFieldBridges

end
