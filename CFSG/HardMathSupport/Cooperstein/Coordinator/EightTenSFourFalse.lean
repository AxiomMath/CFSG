module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenResidualSplit
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.Assembly

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

theorem eightTenNodeSFour : EightTenNodeSFour := by
  intro G _ _ X S L hX hA hL m hm e hN θ hNS hθS r hr1 hrs hgood e4 he4
  have hSL : S ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_isWeakSBlock hX hA hL
  have hA' : Asc81bHyp (L ⊔ S) S := asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
  obtain ⟨π, hπ, hker, hAlt, hequiv, hθV⟩ := hNS
  exfalso
  exact s_four_false_assembled hA' hSL (r := r) (d := m) (by omega) e4 π θ hπ hker hAlt hequiv
    hθV hθS he4 hL.perfect

end CFSG.HardMathSupport.Cooperstein.Coordinator
