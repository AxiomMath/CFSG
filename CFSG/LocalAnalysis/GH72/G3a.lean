module

public import CFSG.LocalAnalysis.GH72.G3aOdd
public import CFSG.LocalAnalysis.GH72.G3aAlperin

public section

namespace CFSG.GH72

namespace Sec3Setting

variable {G : Type*} [Group G] [Finite G]

theorem lemma_3_1 (𝔖 : Sec3Setting G) (A B : Subgroup G) (hAS : A ≤ 𝔖.S) (hBS : B ≤ 𝔖.S)
    (hA : IsE16 A) (hB : IsE16 B) (g : G)
    (hg : A.map (MulAut.conj g).toMonoidHom = B) :
    ∃ s ∈ (𝔖.S : Subgroup G), A.map (MulAut.conj s).toMonoidHom = B :=
  lemma_3_1_of_odd 𝔖
    (fun _D _D₁ _D₂ B' u hd hB' hB16 huN huodd =>
      odd_normalizes_e16_of_dd hd huodd huN hB' hB16)
    A B hAS hBS hA hB g hg

end Sec3Setting

end CFSG.GH72
