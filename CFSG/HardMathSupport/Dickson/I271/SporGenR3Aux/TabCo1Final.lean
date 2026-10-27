module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Plane
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1FiveB
public import Certificates.Certificate13670

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Block CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F CFSG.Open
  CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Dickson.I271

section Final


theorem tabCo1_centShapeMulti (hOut : SporadicOuterLeTwo) (hG : GOK) :
    CentShapeMulti 5 (GoodSpor 5 [.J2]) (RkSpor 5 [.J2]) ↥GA := by
  haveI : Finite ↥GA := finite_GA
  refine ⟨fun k hk1 hk5 => ?_, fun E hE hnc => tabCo1_plane hOut hG E hE hnc⟩
  have hord : orderOf k = 5 := orderOf_eq_prime hk5 hk1
  obtain ⟨c, h0 | h1 | h5⟩ := tabCo1_census hG k hord
  · exact multiShapeAt_conj_back Nat.prime_five (fun _ _ _ _ e h => GoodSpor.of_equiv e h)
      (fun _ _ _ _ e h => RkSpor.of_equiv e h)
      (multiShapeAt_of_shapeRkAt Nat.prime_five (tabCo1_fiveA hOut _ h0))
  · exact multiShapeAt_conj_back Nat.prime_five (fun _ _ _ _ e h => GoodSpor.of_equiv e h)
      (fun _ _ _ _ e h => RkSpor.of_equiv e h) (tabCo1_fiveB _ h1)
  · exact multiShapeAt_conj_back Nat.prime_five (fun _ _ _ _ e h => GoodSpor.of_equiv e h)
      (fun _ _ _ _ e h => RkSpor.of_equiv e h) (Or.inl (tabCo1_fiveC _ h5))

theorem centShapeMulti_Co1_five (hOut : SporadicOuterLeTwo) :
    CentShapeMulti 5 (GoodSpor 5 [.J2]) (RkSpor 5 [.J2]) (NativeSporadic.Carrier .Co1) := by
  haveI : Finite ↥GA := finite_GA
  haveI : Finite (NativeSporadic.Carrier .Co1) :=
    CFSG.Sporadic.finite_carrier_of_ne_M .Co1 (by decide)
  have hG : GOK := Certificates.certificate13670
  have h := tabCo1_centShapeMulti hOut hG
  have e : ↥GA ≃* NativeSporadic.Carrier .Co1 := co1MatEquiv.symm
  exact CentShapeMulti.of_equiv (Q := ↥GA) (Q' := NativeSporadic.Carrier .Co1) Nat.prime_five
    (fun _ _ _ _ e h => GoodSpor.of_equiv e h) (fun _ _ _ _ e h => RkSpor.of_equiv e h) e h

end Final

end CFSG.HardMathSupport.Dickson.I271.TabCo1
