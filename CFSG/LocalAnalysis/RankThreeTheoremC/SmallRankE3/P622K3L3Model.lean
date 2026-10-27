module

public import CFSG.Adapters.TauCetiLieModels
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.RankThree.PartOne.SRC.ModelL3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open scoped MatrixGroups

theorem exists_sl2_embedding_of_A2 {X : Type} [Group X] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A 2 q).Valid)
    (e : X ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.A 2 q, hv⟩) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = q.p ^ q.exponent ∧
      ∃ ι : SL(2, F₀) →* X, Function.Injective ι := by
  obtain ⟨_, hcl | ⟨hn, _⟩⟩ := CFSG.Models.lieModel_A 2 q hv e
  · obtain ⟨_, K, hK, hfin, hcard, ⟨φ⟩⟩ := hcl
    let P := CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K
    refine ⟨K, hK, hfin, hcard,
      φ.symm.toMonoidHom.comp (P.toMonoidHom.comp (CFSG.RankThree.PartOne.SRC.psl3Emb (F := K))),
      ?_⟩
    intro a b hab
    have h1 : φ.symm (P (CFSG.RankThree.PartOne.SRC.psl3Emb (F := K) a)) =
        φ.symm (P (CFSG.RankThree.PartOne.SRC.psl3Emb (F := K) b)) := hab
    have h2 := P.injective (φ.symm.injective h1)
    exact CFSG.RankThree.PartOne.SRC.psl3Emb_injective h2
  · exact absurd hn (by omega)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
