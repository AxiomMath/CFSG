module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Final1
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Model
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44GL
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Syl
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Abs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Simple
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Golay

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Sporadic.Fi23 CFSG.Blueprint.NativeSporadic

set_option linter.unusedSectionVars false

theorem cocodeMain_final : S44.CocodeMainStmt :=
  S44.cocodeMain S44.glDvd S44.noCard2047 S44.orbit23 (S44.simpleOfShape S44.idxDvd11)

theorem stage44'_final (R : Fi22CoverRest) : Stage44' := by
  obtain ⟨O, hF⟩ := frameModel_Cd R card_permStab_golay_zero_le
  exact stage44'_core cocodeMain_final (localModel_Cd R) hF
    (fun Λ _ hq h2 hQ τ hτ hτ1 => by
      obtain ⟨ψ, hψ⟩ := exists_iso_Cd hq h2 hQ hτ hτ1
      exact ⟨ψ, Subtype.ext hψ⟩)

end CFSG.EvenSporadicStandard.TwoFi22.DS81
