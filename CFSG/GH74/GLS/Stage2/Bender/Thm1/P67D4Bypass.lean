module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4BadCase

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem d4_false_of_outer_three_q1 (hA2 : D4OuterThreeA2Toral)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 1)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f))
    {V Z : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))}
    (h2 : N2Cfg (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) 3 V Z)
    (h3 : N3Full (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) V Z)
    (hout : ∃ φ ∈ V, φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) : False :=
  d4_false_of_outer_three_q1_of_bad hA2 d4BadCase_thm hp hp2 hp3 hf hq K hK σ hσ h2 h3 hout

end CFSG.GH74.GLS.Stage2.Bender.Thm1
