module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BLocalEps
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AGap
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AModel
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.RankThree.PartTwo.Sec4 CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns

theorem i253_any_of_isSL3Eps {X : Type} [Group X] [Finite X] (hq : CFSG.Open.IsQuasisimple X)
    (h : Lemma27Ns.IsSL3Eps X) : IsSLThreeEpsAny X := by
  obtain ⟨π, p, f, K, hF, φ, hK, hmod, hφ⟩ := l3b_model_of_isSL3Eps h
  let e : X ≃* ↥(slPi π 3 (p ^ f) K) := MulEquiv.ofBijective
    (φ.codRestrict (slPi π 3 (p ^ f) K) hφ.mem_sl)
    ⟨fun x y hxy => hφ.inj (congrArg Subtype.val hxy), fun ⟨s, hs⟩ => by
      obtain ⟨x, hx⟩ := hφ.exists_of_mem_sl hs
      exact ⟨x, Subtype.ext hx⟩⟩
  have h2 : 2 < p ^ f := by
    by_contra hle
    have hp := hK.prime
    have hf1 := hK.one_le
    have h2le : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    have heq : p ^ f = 2 := by omega
    cases π
    · haveI := (isSolvable_slPi_false_two hK heq).1
      exact false_of_quasisimple_of_solvable hq
        (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
    · have : ModThree true (p ^ f) := hmod
      simp only [ModThree, Bool.cond_true] at this
      omega
  exact isSLThreeEpsAny_of_mulEquiv e.symm (isSLThreeEpsAny_slPi hK hmod h2)

end CFSG.HardMathSupport.Solomon.Coordinator
