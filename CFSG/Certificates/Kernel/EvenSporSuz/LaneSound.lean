module

public import CFSG.Certificates.Kernel.Misc.Spec.F3Lanes
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.Mat

public section

namespace CFSG.KC.EvenSporSuz

open CFSG.KC.Misc.Spec

@[expose] def lanesMt (A : CFSG.EvenSporadicStandard.TwoSuz.Mt) : ℕ :=
  lanes 144 fun t => A.getD t 0

theorem getD_lt_of_canonB {A : CFSG.EvenSporadicStandard.TwoSuz.Mt}
    (hA : CFSG.EvenSporadicStandard.TwoSuz.canonB A = true) {t : ℕ} (ht : t < 144) :
    A.getD t 0 < 3 := by
  simp only [CFSG.EvenSporadicStandard.TwoSuz.canonB, Bool.and_eq_true, beq_iff_eq,
    Array.all_eq_true, decide_eq_true_eq] at hA
  have hs : t < A.size := by omega
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs, Option.getD_some]
  exact hA.2 t hs

theorem canon3_lanesMt {A : CFSG.EvenSporadicStandard.TwoSuz.Mt}
    (hA : CFSG.EvenSporadicStandard.TwoSuz.canonB A = true) : Canon3 (lanesMt A) :=
  canon3_iff.2 ⟨_, fun _ ht => getD_lt_of_canonB hA ht, rfl⟩

theorem pkMat3_lanesMt {A : CFSG.EvenSporadicStandard.TwoSuz.Mt}
    (hA : CFSG.EvenSporadicStandard.TwoSuz.canonB A = true) :
    pkMat3 (lanesMt A) = CFSG.EvenSporadicStandard.TwoSuz.ofMt A := by
  ext i j
  rw [lanesMt, pkMat3_lanes fun _ ht => getD_lt_of_canonB hA ht]
  rfl

theorem mulF3_lanesMt {A B : CFSG.EvenSporadicStandard.TwoSuz.Mt}
    (hA : CFSG.EvenSporadicStandard.TwoSuz.canonB A = true)
    (hB : CFSG.EvenSporadicStandard.TwoSuz.canonB B = true) :
    CFSG.KC.Misc.G24.mulF3 (lanesMt A) (lanesMt B) =
      lanesMt (CFSG.EvenSporadicStandard.TwoSuz.mulM A B) := by
  obtain ⟨hc, hm⟩ := canon3_mulF3 (canon3_lanesMt hA) (canon3_lanesMt hB)
  have hAB := CFSG.EvenSporadicStandard.TwoSuz.canonB_mulM A B
  refine canon3_inj hc (canon3_lanesMt hAB) ?_
  rw [hm, pkMat3_lanesMt hA, pkMat3_lanesMt hB, pkMat3_lanesMt hAB,
    CFSG.EvenSporadicStandard.TwoSuz.ofMt_mulM]

theorem lanesMt_oneM :
    lanesMt CFSG.EvenSporadicStandard.TwoSuz.oneM = CFSG.KC.Misc.G24.one3 := by
  have h1 := CFSG.EvenSporadicStandard.TwoSuz.canonB_oneM
  refine canon3_inj (canon3_lanesMt h1) canon3_one3.1 ?_
  rw [pkMat3_lanesMt h1, canon3_one3.2, CFSG.EvenSporadicStandard.TwoSuz.ofMt_oneM]

end CFSG.KC.EvenSporSuz
