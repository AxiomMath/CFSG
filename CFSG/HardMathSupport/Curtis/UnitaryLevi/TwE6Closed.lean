module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.TwE6Cent
public import CFSG.HardMathSupport.Foote.E27.SporCentKill
public import CFSG.HardMathSupport.Curtis.Coordinator.ExcLeafDefs

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration TauCeti
open CFSG.HardMathSupport.Malle.E27Lie (InnerLeaf)
open CFSG.HardMathSupport.Curtis.Coordinator.ExcLeaf (IdxExc)


theorem innerLeaf_twistedE6_one : InnerLeaf (IdxExc .twistedE6 1) := by
  intro X _ _ K R T z h hz d hd e
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, hq, hr, rfl⟩ := hd
  obtain ⟨ψ⟩ := e
  obtain ⟨F, _, σ, hF, hσ, ⟨ε⟩⟩ := exists_catEquiv_twistedE6 q hv
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hq3 : (q.p ^ q.exponent) % 3 = 1 := by rw [← hqc]; exact hr
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by
    rw [hF]; exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  have : Finite (ModGL TwistTag.E6.tag F) := inferInstance
  have : Finite ↥(twistedE6RootGroup F σ) := inferInstance
  obtain ⟨Q, hQ, hk⟩ := exists_sylow_centralizer_kill_twE6 F σ.toRingHom q.prime_p
    q.exponent_pos hF (fun c => by simpa using hσ c) hq3
  exact h.false_of_centralizer_kill hz (ψ.trans ε) Q hQ hk

end CFSG.HardMathSupport.Curtis.UnitaryLevi

end
