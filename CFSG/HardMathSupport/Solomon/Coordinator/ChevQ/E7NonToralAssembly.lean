module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCubeBlocks
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralBlockCore

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.AlgebraicGroups

set_option linter.unusedSectionVars false

section Assembly


theorem e7NonToralTwoNormalizes_of_blocks (hB : E7ThreeKilledPlaneBlocks) :
    E7NonToralTwoNormalizes := by
  intro K _ _ hK _ E₀ hE₀ hc hD
  have hK3 : ¬ 3 ∣ Nat.card K := by omega
  obtain ⟨P, hPE, hPc, z, hzE, -, hE⟩ := exists_plane_element hc
  have hPexp : ∀ x ∈ P, x ^ 3 = 1 := fun x hx => hE₀.2 x (hPE hx)
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, c, hcP⟩ := langToralPlane_E7_three K hK3 P hPexp hPc
  let D : LangPlaneData .E7 K P := ⟨w, Fr, hFr, g0, hg0C, hg0, c, hcP⟩
  obtain ⟨α, hα, hkα⟩ := langPlaneKilled_E7 K hK3 P hPexp hPc D
  obtain ⟨F⟩ := nonempty_cubeFrame hK3 hE₀ hc hPE hPc D hzE
  have hker : (familyKernel (τ := Tag.E7) F.a).Nonempty := ⟨α, F.kills α hα hkα⟩
  rcases hB (AlgebraicClosure K) F.a F.exp3 hker F.ω F.ω_stab with hω | ⟨B, hBω⟩
  · exact (hD.false (F.nonempty_langPlaneData
      (monomialToralAt_three_of_block a2BlockToral_E7) hK3 hE₀ hzE hE hω).some).elim
  · exact F.normalizes_of_blocks (Or.inl rfl) nonToralBlockCore_holds hE₀ hPE hzE hE B hBω

end Assembly

section Rest


theorem e7NonToralTwoRest_of_blocks (hB : E7ThreeKilledPlaneBlocks) :
    SeitzExcOpenRest5.E7NonToralTwoRest :=
  e7NonToralTwoRest_of_normalizes (e7NonToralTwoNormalizes_of_blocks hB)

end Rest

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore

end
