module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Pair

public section

namespace CFSG.AGLEmbedding

theorem D1PhaseThree.toPair {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}
    {M H R : Subgroup G} (h : D1PhaseThree p P M H R) : CFSG.AGLEmbeddingD2.AGLPair p M H R where
  glob := h.glob
  prime := h.prime
  ne_two := h.ne_two
  maxTwoLocal_M := h.maxTwoLocal_M
  maxTwoLocal_H := h.maxTwoLocal_H
  le_H := h.le_H
  le_M := h.le_M
  isSylow := h.isSylow
  not_le := h.not_le
  primeCore_le := h.primeCore_le
  twoCore_inf := h.twoCore_inf

end CFSG.AGLEmbedding
