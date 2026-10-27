module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscThmE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf67Print

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Inner

section Bridge

variable {r n : ℕ}

theorem Perp22.thmER_of_twinThmER (h : TwinThmER r n) : Perp22.ThmER r n := by
  intro Y _ _ R S t hP K H hK hH
  have hΩ := hP.core.hyp
  have hU : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hP.core.datum
  obtain ⟨g, rfl⟩ := hK
  obtain ⟨K', hK', hne⟩ := hP.core.twin
  have hKΩ : conjSub g (tightCore R) ∈ CoreAssembly.conjClass (tightCore R) := ⟨g, rfl⟩
  have hKt : IsUniqueInvolution (conjSub g (tightCore R)) (g * t * g⁻¹) := hU.conj g
  have hK'g : conjSub g K' ∈ twinSet (CoreAssembly.conjClass (tightCore R))
      (conjSub g (tightCore R)) := by
    obtain ⟨hK'Ω, z, hzR, hzK'⟩ := hK'
    have hzt : t = z := hU.eq hzR
    subst hzt
    exact ⟨hΩ.conjInvariant g K' hK'Ω, g * t * g⁻¹, hKt, hzK'.conj g⟩
  have hne' : conjSub g K' ≠ conjSub g (tightCore R) := fun e => hne (Generic.conjSub_injective g e)
  obtain ⟨W, hW, -⟩ := TwinPerpV3.exists_printedWT hΩ hKΩ hK'g hne'
  exact h Y R S t hP.core _ H W hKΩ hW
    ⟨hH.trans, fun L hL J hJ R₁ R₂ hR₁ hR₁L hR₂ hR₂J hc a ha _ ha1 ha2 =>
      hH.cent L hL J hJ R₁ R₂ hR₁ hR₁L hR₂ hR₂J hc a ha ha1 ha2⟩

end Bridge

end CFSG.CGT.PushingUpLit.SolKNA.R4
