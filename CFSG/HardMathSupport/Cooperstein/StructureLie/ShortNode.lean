module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShortCommutator
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShortClauses
public import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptL

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock barM IsClassicalTwoOrG2 IsOrthogonalTwo)

theorem eightEightShort : EightEightShort := by
  intro G _ _ X S L hX hA hL hc ht hirr
  have hQV := commutator_pCore_le_blockV hX hA hL ht
  have hZ := centre_barM_trivial hX hA hL ht hQV
  have hshort := isShort2_of_hQV hX hA hL ht hirr hQV
  refine ⟨fun _ => ⟨hshort, isTypeScriptL_of_transvectionData hX hA hL ht hQV hZ⟩, fun h3 => ?_⟩
  exact absurd h3.1 (card_center_barM_ne_three hX hA hL ht hQV)

end CFSG.HardMathSupport.Cooperstein.StructureLie
