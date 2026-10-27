module

public import CFSG.GH74.GLS.Stage2.Final.ClassicalF
public import CFSG.GH74.GLS.Stage2.Final.ClassicalMax6A

public section

namespace CFSG.GH74.GLS.Stage2.Final

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Main

theorem stageFiveClassical_of_stage1Out (hF : ClassicalData) {G : Type} [Group G] [Finite G] {z : G}
    {S : Subgroup G} {k : Kind} (hStd : Std G) (hk : k = Kind.psp4 ∨ ∃ ε : Bool, k = Kind.l4 ε)
    (h1 : Stage1Out G z S k) (h2 : Stage2Out G z k S) : StageFiveClassical G := by
  rcases hk with rfl | ⟨ε, rfl⟩
  · cases h1 with
    | psp4 h q L₁ L₂ hq ht =>
      exact stageFiveClassical_of_psp4 hF.center hF.ecInter hF.disjoint (h.toCtx' hStd) h2 ht
  · cases h1 with
    | l4NF _ h q L₁ L₂ hq hq4 w hw ht =>
      refine stageFiveClassical_of_l4NF hF.center hF.ecInter hF.disjoint hF.oddCore (h.toCtx' hStd) h2 hq hq4 ht hw ?_
      intro p f hp hpf
      exact max6A_of_sixA (h.toCtx' hStd) (h2.sixA ε q L₁ L₂ rfl hq p f hp hpf)
    | l4F _ h q L₁ L₂ hq ht =>
      refine stageFiveClassical_of_l4F hF.center hF.ecInter hF.disjoint hF.oddCore hF.oneClass hF.layerBar
        (h.toCtx' hStd) h2 hq ht ?_
      intro p f hp hpf
      exact max6A_of_sixA (h.toCtx' hStd) (h2.sixA ε q L₁ L₂ rfl hq p f hp hpf)

end CFSG.GH74.GLS.Stage2.Final
