module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.TypeIExteriorTi

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.Proofs

open CFSG.FeitThompson Subgroup
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep09

universe u

theorem FTS_supporting_type_two_forces_frobenius
    (h₁ : Statements.FNI_p_configuration_kappa_factors.{u})
    (h₂ : Statements.FTS_kappa_positive_support_forces_cyclic_frobenius.{u})
    (h₃ : Statements.FTS_type_I_complement_structure.{u})
    (h₄ : Statements.FTS_type_I_core_kappa_identity.{u}) :
    Statements.FTS_supporting_type_two_forces_frobenius.{u} := by
  intro G _ _ hG M hM hMI a ha hCM T hT hTII
  obtain ⟨haM, ha1, hacent⟩ := ha
  obtain ⟨-, hHS, -⟩ := h₄ G hG M hM hMI
  have hosm : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hamb : IsFTAmbient G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have haH : a ∈ hallCoreIn M := by
    by_contra haH
    have hD : a ∈ exteriorFixedSet (hallCoreIn M) M := ⟨haM, haH, hacent⟩
    obtain ⟨-, -, hfus⟩ := FTS_type_I_exterior_ti h₃ h₄ G hG M hM hMI ⟨a, hD⟩
    refine hCM fun g hg => hfus a hD a hD g ?_
    have hc : a * g = g * a := (Subgroup.mem_centralizer_iff.1 hg) a rfl
    calc g⁻¹ * a * g = g⁻¹ * (a * g) := by group
      _ = g⁻¹ * (g * a) := by rw [hc]
      _ = a := by group
  obtain ⟨E₀, W₁, W₂, hcfg, -⟩ := hTII.exists_isPConfigurationIIToIV
  obtain ⟨hkT, -, -⟩ :=
    h₁ G hosm T E₀ W₁ W₂ hT.isCoatom hcfg.isWitnessedPConfiguration
  obtain ⟨-, -, -, ⟨E, hEM, hSne, hEne, hsemi, -, hfix⟩, -⟩ :=
    h₂ G hamb M hM T hT.isCoatom a (hHS ▸ haH) ha1 hCM hT.le hkT
  exact ⟨E, hEM, hHS ▸ hSne, hEne, hHS ▸ hsemi, fun e he he1 => hHS ▸ hfix e he he1⟩

end CFSG.FeitThompson.Proofs

end
