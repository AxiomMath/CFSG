module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearAut
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearTwo
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.UnitaryAut
public import CFSG.Yardstones.Md42047359a2a.Definitions
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open TauCeti CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

theorem lieSemisimpleCentLinearUnitary :
    CFSG.Yardstones.Md42047359a2a.LieSemisimpleCentLinearUnitary := by
  intro S _ _ _ _ idx hF he p hp hp2 hpc β hβp _
  obtain ⟨e⟩ := he
  obtain ⟨d, hv⟩ := idx
  cases d with
  | A r q =>
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
    let e' : S ≃* LinearFlag.projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
      e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _))
    have hpq : p ≠ q.p := by
      have h1 : (LieTypeIndex.A r q).characteristic = q.p := LieTypeIndex.characteristic_A r q
      exact h1 ▸ hpc
    have hpK : (p : GaloisField q.p q.exponent) ≠ 0 := by
      intro h0
      rw [CharP.cast_eq_zero_iff (GaloisField q.p q.exponent) q.p] at h0
      exact hpq ((Nat.prime_dvd_prime_iff_eq q.prime_p hp).mp h0).symm
    refine perfectInLayer_of_congr e' β ?_
    have hβ' : MulAut.congr e' β ^ p = 1 := by rw [← map_pow, hβp, map_one]
    rcases Nat.lt_or_ge r 2 with hr2 | hr2
    · obtain rfl : r = 1 := by omega
      exact perfectInLayer_projectiveSL_two hp hpK _ hβ'
    · exact perfectInLayer_projectiveSL (by omega) hp hp2 hpK _ hβ'
  | twistedA r q =>
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    obtain ⟨⟨hℓ, hf, hn3, hq⟩, K, _, _, hK, ⟨eT⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := r + 1) (K := K))
    let e' : S ≃* primeFormP h (idGram K (r + 1)) :=
      (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
    have hpq : p ≠ q.p := by
      have h1 : (LieTypeIndex.twistedA r q).characteristic = q.p :=
        LieTypeIndex.characteristic_twistedA r q
      exact h1 ▸ hpc
    refine perfectInLayer_of_congr e' β ?_
    exact perfectInLayer_primeFormP h hn3 (fun h3 => hq (Prod.ext h3.1 h3.2)) hp hp2 hpq _
      (by rw [← map_pow, hβp, map_one])
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hF

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
