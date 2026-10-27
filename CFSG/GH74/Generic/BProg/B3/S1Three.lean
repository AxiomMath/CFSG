module

public import CFSG.GH74.Generic.BProg.B3.S1ThreeAlpha
public import CFSG.GH74.Generic.BProg.B3.S1ThreeBeta
public import CFSG.GH74.Generic.BProg.B3.S1ThreePerf
public import CFSG.GH74.Generic.BProg.B3.S1FinalMain
public import CFSG.GH74.Generic.BProg.B3.KG531BPairOther

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup

namespace S1Three

section Three

variable {G : Type} [Group G] [Finite G]


theorem false_of_ctx_s1_three
    {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}
    (hc : Ctx21 G x K A a D J) (h3 : B1.PilotS1.QShape1Three (↥K ⧸ pPrimeCore 2 ↥K)) : False := by
  have h1 : QShape1 (↥K ⧸ pPrimeCore 2 ↥K) := by
    obtain ⟨F, _, _, hF3, e⟩ := h3
    exact Or.inl ⟨F, inferInstance, inferInstance, by omega, e⟩
  obtain ⟨φA, φB, hd⟩ := exists_s1ThreeData hc h3
  obtain ⟨hB, hA | hA⟩ := s1three_reduce hc h1 hd
  · exact s1three_beta hc h1 hd hB hA
  · exact s1three_alpha hc h1 hd hB hA (s1three_perfectFree hc h3)

end Three

end S1Three

section Shape1


theorem stage1BalFor_shape1
    (hNine : KG531BP.KG531BPairNine) : Stage1BalFor QShape1 := by
  refine stage1BalFor_of_ctx (fun G _ _ x K A a D J hc h1 => ?_)
  rcases B1.PilotS1.qShape1_split h1 with hbig | h3
  · exact S1FinalMain.false_of_ctx_s1_big
      (KG531BP.kg531BPair_of_parts KG531BP.kg531BPairOther_proved hNine) hc hbig
  · exact S1Three.false_of_ctx_s1_three hc h3

end Shape1

end CFSG.GH74.Generic.BProg.B3
