module

public import CFSG.LocalAnalysis.EvenBN.G2.FieldMain
public import CFSG.LocalAnalysis.EvenBN.G2.ProductMain
public import CFSG.LocalAnalysis.EvenBN.G2.LocalN60Four

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases (xor_of_exactClosure)


namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {K : Type} [Field K]
  [Finite K] [CharP K 2]

theorem false_of_qFacts (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hA : ∃ A : Subgroup G, Complement₂ d t A) :
    False := by
  obtain ⟨hsyl₂, -, α₂, hex₂⟩ := h.yamada_5_59_N₂ hW d hK hQ
  obtain ⟨hsyl₁, -, α₁, hex₁⟩ := h.yamada_5_59_N₁ hW d hK hQ
  rcases xor_of_exactClosure hex₂ with ⟨hPa, -⟩ | ⟨hFa, -⟩
  · exact h.false_of_productHyp hW d hK hQ
      ⟨hsyl₁, hsyl₂, ⟨α₁, hex₁⟩, ⟨α₂, hex₂, hPa⟩, h.yamada_5_60_1 hW d hK hQ,
        h.yamada_5_60_3_le hW d hK hQ, hA⟩
  · exact h.false_of_fieldCase hW d hK hQ hsyl₂ hex₂ hFa

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
