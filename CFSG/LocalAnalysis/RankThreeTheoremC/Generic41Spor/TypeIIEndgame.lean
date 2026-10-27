module

import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIIEndgame41Main
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem typeII_endgame41 (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    {p : ℕ} (hp : p ∈ rankThreeSigmaA G) (h5 : 5 ≤ p) {P : Sylow p G} {M : Subgroup G}
    (hM : IsCoreMaxLocal p P M) {x : G} (hxP : x ∈ (P : Subgroup G)) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    {U : Subgroup G} (hU : IsElemAbelian p U) (hUc : Nat.card U = p ^ 2)
    (hUP : U ≤ (P : Subgroup G)) (hxU : x ∈ U)
    (hF : ∀ F : Subgroup G, IsPGroup p F → U ≤ F → F ≤ M → CFSG.Open.pRank p F ≤ 2 →
      IsMulCommutative F ∧ ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ F →
        (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x)
    (hC : ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M)
    (hL43 : ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → U ≤ normalizer (Y : Set G) →
      IsSylowOf 2 (Y ⊓ rankThreePrimeCore p M) (rankThreePrimeCore p M) → normalizer (Y : Set G) ≤ M)
    (hL45 : ∃ S₁ : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁ ∧ ¬ S₁ ≤ M)
    (hL44 : ∀ X : Subgroup G, IsPGroup 2 X → X ≤ rankThreePrimeCore p M →
      X ≤ centralizer ({x} : Set G) → X = ⊥) : False := by
  haveI : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  exact eg41_false_of_plane hS hU0 hD1 hInn hWC hp (by omega) hM hx1 hxp hU hUc hUP hxU hF hC hL43
    hL45 hL44

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
