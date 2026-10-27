module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlus
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatch

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding

section Small


theorem altIbCell_small (hGA : CFSG.Open.GriessAllModelsStatement) :
    AltIbCell IsSmallTwoOrG2 := by
  intro Y _ _ L J hL _ hX _ _ _ p hp57 _ x _ _ _ W _ _ _ hE
  obtain ⟨E, hEW, -, hEcard⟩ := hE
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hp5 : 5 ≤ p := by rcases hp57 with rfl | rfl <;> norm_num
  exact false_of_small_ib hGA hL.2.2 hp hp5 hX (hEW.trans inf_le_right) hEcard

end Small

section Cells


theorem altIbCell_g2 (hSch : KFactCatalogSchreier)
    (hGA : CFSG.Open.GriessAllModelsStatement) : AltIbCell (IsLieOf IdxG2) := by
  intro Y _ _ L J hL htype hX hpar hJL hnB p hp57 _ x hxL hxp hfix W hW hWN hWx hE
  obtain ⟨E, hEW, hEel, hEcard⟩ := hE
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hp5 : 5 ≤ p := by rcases hp57 with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p E := IsPGroup.of_card hEcard
  obtain ⟨hpZ, V, hVle, hV, hEV⟩ := exists_perfect_core_in_parabolic hSch hGA hL htype
    (Or.inr (Or.inr (Or.inr (Or.inl hX)))) hp hp5 hxL hfix hW hWN hWx hEW hEp
  exact false_of_card_sq_perfect_g2 ⟨hL, htype, hpar, hJL, hnB⟩ hX hp (by omega) hpZ
    (fun v hv => (hVle hv).1) hV hEV hEcard hEel.2

theorem kFactBlockToralAltIb_of_cells (hSch : KFactCatalogSchreier)
    (hGA : CFSG.Open.GriessAllModelsStatement) (hA : AltIbCell (IsLieOf IdxA))
    (hTA : AltIbCell (IsLieOf IdxTwistedA)) : KFactBlockToralAltIb := by
  intro Y _ _ L J hL hcl hpar hJL hnb p hp57 hAlt x hxL hxp _ hfix W hW hWN hWx hE
  rcases isClassicalTwoOrG2_family_cases hcl with h | h | h | h | h | h | h
  · exact hA Y L J hL hcl h hpar hJL hnb p hp57 hAlt x hxL hxp hfix W hW hWN hWx hE
  · exact hTA Y L J hL hcl h hpar hJL hnb p hp57 hAlt x hxL hxp hfix W hW hWN hWx hE
  · exact altIbCell_b hSch hGA Y L J hL hcl h hpar hJL hnb p hp57 hAlt x hxL hxp hfix W hW hWN
      hWx hE
  · exact altIbCell_d hSch hGA Y L J hL hcl h hpar hJL hnb p hp57 hAlt x hxL hxp hfix W hW hWN
      hWx hE
  · exact altIbCell_twistedD hSch hGA Y L J hL hcl h hpar hJL hnb p hp57 hAlt x hxL hxp hfix W hW
      hWN hWx hE
  · exact altIbCell_g2 hSch hGA Y L J hL hcl h hpar hJL hnb p hp57 hAlt x hxL hxp hfix W hW hWN
      hWx hE
  · exact altIbCell_small hGA Y L J hL hcl h hpar hJL hnb p hp57 hAlt x hxL hxp hfix W hW hWN
      hWx hE

end Cells

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
