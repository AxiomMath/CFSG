module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2

@[expose] def AGL81I811 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], AGLGlobal G → ∀ M H : Subgroup G, GLBIsMaxTwoLocal M →
    GLBStronglyEmbedded 3 M → IsTwoLocal H → ∀ L : Subgroup G, L ≤ H ⊓ M →
      CFSG.IsPComponent 3 (L.subgroupOf (H ⊓ M)) → CFSG.Open.pRank 3 L = 1 →
      ∀ A : Subgroup G, Nat.card A = 3 → A ≤ L →
        (∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (A : Set G) ⊓ (H ⊓ M) →
          A.map (MulAut.conj g).toMonoidHom = A) →
        ∀ S : Subgroup G, IsSylowTwoOf S H → (S ⊓ M).relIndex S ≤ 8 →
          ∃ S' : Subgroup G, IsSylowTwoOf S' H ∧ S' ≤ M

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
