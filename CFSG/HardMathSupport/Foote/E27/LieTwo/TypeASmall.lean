module

public import CFSG.HardMathSupport.Foote.E27.LieTwo.LinearSmall
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.Index

public section

namespace CFSG.HardMathSupport.Foote.E27

open TauCeti

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem E27Config.false_of_typeA_two_small (h : E27Config X K R T z) (hz : z ∈ K) {r : ℕ}
    {q : PrimePower} (hv : (LieTypeIndex.A r q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.A r q, hv⟩)) (hq : q.p ^ q.exponent = 2)
    (hr : r = 2 ∨ r = 3) : False := by
  obtain ⟨e⟩ := e
  exact h.false_of_psl_two_small hz
    (CFSG.HardMathSupport.Malle.E27Lie.statedClassicalModel_typeA' hv e) hq
    (by rcases hr with rfl | rfl <;> simp)

end CFSG.HardMathSupport.Foote.E27
