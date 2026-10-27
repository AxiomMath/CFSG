module

public import CFSG.LieType.Steinberg.CentralExt.SpinMinusCenter
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.LieType.Steinberg.CentralExt.SL2CentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusCentrallyClosed
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

namespace CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed

variable {n : ℕ} {K : Type} [Field K] {b c : K}

theorem pomegaMinus_hopfMultiplier
    [Finite K] {p f : ℕ} (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = p ^ f) (hK4 : 4 ≤ Nat.card K) :
    commutator (StatedProj (StatedOmega (StatedQuadMinus n K b c))) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier
        (StatedProj (StatedOmega (StatedQuadMinus n K b c))) ≃*
          Multiplicative (ZMod (Nat.gcd 4 ((p ^ f) ^ n + 1)))) := by
  set q := spinToStatedProj (quadMinus n K b c) (range_spinMatrix_quadMinus hn hirr)
  obtain ⟨hq, hkerZ, hker⟩ := spinToStatedProj_quadMinus (K := K) hn hirr
  have : Group.IsPerfect (spinGroup (quadMinus n K b c)) := isPerfect_spinGroup_quadMinus hn hirr
  have hperf : Group.IsPerfect (StatedProj (StatedOmega (StatedQuadMinus n K b c))) :=
    Group.IsPerfect.ofSurjective hq
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  have : Finite (CFSG.RankThree.PerfectCover.HopfCover
      (StatedProj (StatedOmega (StatedQuadMinus n K b c)))) :=
    CFSG.RankThree.PerfectCover.finite_hopfCover hperf
  have e1 : CFSG.RankThree.PerfectCover.hopfMultiplier
      (StatedProj (StatedOmega (StatedQuadMinus n K b c))) ≃* q.ker :=
    MulEquiv.ofBijective _ (SL2Closed.hopfMultiplierToKer_bijective q hq hker.le
      fun π hπ hcen => spinMinus_exists_section_of_central hirr hn hK4 hπ hcen)
  obtain ⟨hcard, hcyc⟩ := card_scalarSpinM hirr hn hK
  rw [← hcard]
  exact ⟨(CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).trans
    (e1.trans ((MulEquiv.subgroupCongr hkerZ).trans (zmodCyclicMulEquiv hcyc).symm))⟩

end CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed
