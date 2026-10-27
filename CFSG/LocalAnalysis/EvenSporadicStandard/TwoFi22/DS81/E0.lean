module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameJMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.SqCert
public import CFSG.Sporadic.Fi23.StarKernel

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Sporadic.Fi23 FrameJ

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def E0 :
    Subgroup ↥Cd :=
  fjHom.range.subgroupOf Cd

theorem Cd_sq :
    ∀ a : ↥Cd, a ^ 2 ∈ center ↥Cd → a ^ 2 = 1 := by
  intro a ha
  rw [center_C] at ha
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 ha
  have hk' : d ^ k = ((a ^ 2 : Cd) : J) := by
    have := congrArg Subtype.val hk
    rwa [Subgroup.coe_zpow] at this
  rcases d_zpow k with h | h
  · apply Subtype.ext
    rw [← hk', h]
    rfl
  · exfalso
    have h2 : ((a ^ 2 : Cd) : J) = d := hk'.symm.trans h
    apply sqStatement_d.1 (a : J)
    rw [← sq]
    simpa [Subgroup.coe_pow] using h2

end CFSG.EvenSporadicStandard.TwoFi22.DS81
