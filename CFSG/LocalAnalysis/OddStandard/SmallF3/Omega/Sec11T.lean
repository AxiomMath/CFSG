module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11TC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11TA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11TB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Alt2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Step111T_of (hp : Asc82Pre11) : Asc82Step111T := by
  intro G _ _ t L S z K1 K2 T hctx hyp hT hST
  have hzt : z * t = t * z :=
    Subgroup.mem_centralizer_singleton_iff.mp (hctx.sylow.1 hctx.mem_S)
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have ht2 : t * t = 1 := by
    rw [← sq]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hctx.involution)
  have hz2' : z * z = 1 := by
    rw [← sq]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hz2)
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have h6 := sec11_class_card_six hp.r10.l1011 hctx hyp
  have hidx := sec11_relIndex_S_T hT hST hctx.sylow h6
  have hclass := sec11_class_T hp.s3.l37 hp.r10.l103 hctx hT.2.1 hST hidx
  have hTK0 := sec11_T_normalizes_K0 ht2 hz2' hzt.symm hz1 hclass
  exact ⟨hidx, hclass, hTK0, sec11_T_normalizes_Q hp.r10.lK0 hp.s3.l36 hp.facts.pockets5
    hp.facts.centZ5 hp.basic hctx hST hidx hTK0⟩

end CFSG.OddStandard.SmallF3.Omega
