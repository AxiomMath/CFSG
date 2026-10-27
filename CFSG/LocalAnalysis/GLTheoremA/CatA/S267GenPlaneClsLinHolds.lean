module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsLinTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.LocalAnalysis.ComponentInitial

theorem genPlaneCompOn_A : GenPlaneCompOn PlaneIdxA := by
  refine genPlaneCompOn_of_planeNoComp fun p d hd hQ => ?_
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have hr : 1 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
    let e' : (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group ≃*
        LinearFlag.projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _)
    have hpq : p ≠ q.p := by
      have h1 : (TauCeti.LieTypeIndex.A r q).characteristic = q.p :=
        TauCeti.LieTypeIndex.characteristic_A r q
      exact h1 ▸ hd.ne
    have hpK : (p : GaloisField q.p q.exponent) ≠ 0 := by
      intro h0
      rw [CharP.cast_eq_zero_iff (GaloisField q.p q.exponent) q.p] at h0
      exact hpq ((Nat.prime_dvd_prime_iff_eq q.prime_p hd.prime).mp h0).symm
    haveI : Finite (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group := Finite.of_equiv _ e'.symm.toEquiv
    refine PlaneNoComp.of_mulEquiv hd.prime e' ?_
    rcases Nat.lt_or_ge r 2 with hr2 | hr2
    · obtain rfl : r = 1 := by omega
      exact planeNoComp_projectiveSL_two hd.prime hpK
    · exact planeNoComp_projectiveSL (by omega) hd.prime hd.odd hpK
  | _ => exact absurd hQ (by simp [PlaneIdxA])

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
