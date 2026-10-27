module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutBig
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutFour

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem outerData_of_involution (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 8)
    (hσ : quadSign Q = 1) {x : OGroup Q} (hx : x * x = 1) (hxΩ : x ∉ omegaGroup hQ) :
    OuterData ↥(omegaProj hQ) (projAut hQ x) := by
  have hle : invDim x ≤ 8 := by
    have := invDim_le x
    omega
  have hne0 : invDim x ≠ 0 := fun h => hxΩ (by
    rw [(invDim_eq_zero_iff hx).mp h]
    exact (omegaGroup hQ).one_mem)
  have hne8 : invDim x ≠ 8 := by
    intro h
    have hxπ : x = piOrth Q := (invDim_eq_finrank_iff hx).mp (by rw [h, hdim])
    apply hxΩ
    rw [hxπ, piOrth_mem_omegaGroup_iff hQ, hdim, hσ]
    exact ⟨by decide, by decide⟩
  have hπd : invDim (piOrth Q * x) = Module.finrank (ZMod 3) V - invDim x :=
    congrArg Prod.fst (invType_piOrth_mul hQ hx)
  by_cases hbig : 5 ≤ invDim x
  · exact outerData_of_big hQ hdim hσ hx hbig (by omega)
  · by_cases h4 : invDim x = 4
    · have hs : invSign x = -1 := by
        rcases Int.units_eq_one_or (invSign x) with h | h
        · exfalso
          apply hxΩ
          refine (involution_mem_omegaGroup_iff hQ hx).mpr ⟨by rw [h4]; decide, ?_⟩
          rw [h, h4]
          decide
        · exact h
      exact outerData_of_four_minus hQ hdim hσ hx (Prod.ext h4 hs)
    · have hd := outerData_of_big hQ hdim hσ (piOrth_mul_mul_self hx)
        (by omega : 5 ≤ invDim (piOrth Q * x)) (by omega : invDim (piOrth Q * x) ≤ 7)
      rwa [projAut_piOrth_mul] at hd

end CFSG.OddStandard.SmallF3.Omega
