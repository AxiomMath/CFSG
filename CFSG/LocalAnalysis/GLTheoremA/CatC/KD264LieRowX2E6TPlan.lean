module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6LAmbient

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T

open CFSG.Open CFSG.Blueprint.Chevalley

section Predicates

@[expose] def PhiU (u : Fin 6 → ZMod 3) : Set (Fin 6 → ℤ) :=
  {α | α ∈ rootsE6 ∧ ∑ i, ((α i : ℤ) : ZMod 3) * u i = 0}

@[expose] def IsPhiComponent (u : Fin 6 → ZMod 3) (C : Set (Fin 6 → ℤ)) : Prop :=
  C ⊆ PhiU u ∧ IsRootConnected C ∧ ∀ D, D ⊆ PhiU u → IsRootConnected D → C ⊆ D → D ⊆ C

@[expose] def PhiTypeA (u : Fin 6 → ZMod 3) : Prop :=
  ∀ C, IsPhiComponent u C → 3 ≤ rootRankQ C → C.ncard = rootRankQ C * (rootRankQ C + 1)

@[expose] def SelA (G : Subgroup (Multiplicative (Fin 6 → ZMod 3))) : Prop :=
  Nat.card G = 9 ∧ ∃ u ∈ G, u ≠ 1 ∧ PhiTypeA (Multiplicative.toAdd u)

@[expose] def SelNA (G : Subgroup (Multiplicative (Fin 6 → ZMod 3))) : Prop :=
  Nat.card G = 9 ∧ ¬ SelA G

end Predicates

section Split


theorem x2e6TorusGood9_of_split (hA : X2E6TorusGoodP SelA) (hN : X2E6TorusGoodP SelNA) :
    X2E6TorusGood9 := by
  intro K _ _ hK σ hσ Ω _ _ _ _ Fr hFr g hg hgn ζ hζ hζ' G hG hRG
  by_cases hs : SelA G
  · exact hA K hK σ hσ Ω Fr hFr g hg hgn ζ hζ hζ' G hs hRG
  · exact hN K hK σ hσ Ω Fr hFr g hg hgn ζ hζ hζ' G ⟨hG, hs⟩ hRG

end Split

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T

end
