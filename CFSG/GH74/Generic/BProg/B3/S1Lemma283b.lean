module

public import CFSG.GH74.Generic.BProg.B3.S1Lemma283bKGB
public import CFSG.GH74.Generic.BProg.B3.KG531

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup

section Lemma283b

variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}

theorem s1_lemma283b_of_pair (hB : KG531BPair) (hc : Ctx21 G x K A a D J)
    (h1 : B1.PilotS1.QShape1Big (↥K ⧸ pPrimeCore 2 ↥K))
    {J₁ J₂ : Subgroup G} (hS : S1SplitMod K A x a J₁ J₂) (hJ₂ : J₂ ≤ J) : ¬ J₁ ≤ J := by
  have _ := h1
  exact s1_lemma283b_of_pair_table kg531Table hB hc hS hJ₂

end Lemma283b

end CFSG.GH74.Generic.BProg.B3
