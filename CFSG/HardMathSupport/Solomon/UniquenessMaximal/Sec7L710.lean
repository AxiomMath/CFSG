module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710Setup
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710Syl
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710Cent
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710XA
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710XB
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710Cover
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710Lift

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710

variable {G : Type} [Group G] [Finite G]

theorem lemma710_of_inputs (hS : GLStanding G 4 3) {B : Subgroup G} (hB : IsBOneMax 3 B)
    (h63 : ∃ M₀ : Subgroup G, Prop63Out B M₀) (h68 : Prop68Out B) (hU : UniqComp B)
    (h75 : Lemma75Stmt B) (h76 : Lemma76Stmt B) (i11 : Input11_6) (l23 : Lemma23)
    (i18 : Input18_10) (i28 : Input28_8) : Lemma710Stmt B := by
  intro T hT K hK
  obtain ⟨M₀, h63⟩ := h63
  obtain ⟨I, hset, hKI, hIK, hYtop⟩ :=
    setup710_exists hS hB h63 h68 hU h75 h76 i11 l23 i18 hT hK
  have hs := sylow_s hset
  have hf : YFacts B T I := ⟨hs, centralizer_s_le hset hs⟩
  obtain ⟨KX, hKXc, hKXl, hKXtop, hKXcard, hlink⟩ := exists_kX hset hf
  obtain ⟨s, hs2, hsi⟩ := i28 (XQ B T I) (xq_isKGroup hS.kProper hYtop)
    (xq_centralizer_le hset hf) KX (tX B T I) (bX B T I) hKXc hKXl (bX_elemAbelian hset)
    (tX_isMax hset hf) hKXtop hKXcard
  refine ⟨s, hs2, fun i hi => ?_⟩
  have hI := cover_of_subset hset hf i (hlink _ (hsi i hi))
  obtain ⟨⟨x₀, hx₀B, hx₀1, hx₀K⟩, -, -⟩ := id hK
  exact covers3_of_cover_I hset.bElem hx₀B hx₀1 (Sec7.le_normalizer_tripleOf hT.2.1 i)
    hset.bnI hx₀K (h68 K hK).lThreeFour hKI hIK hI

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
