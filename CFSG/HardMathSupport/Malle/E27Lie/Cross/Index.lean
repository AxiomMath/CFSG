module

public import CFSG.HardMathSupport.Malle.E27Lie.Cross.LinearIndex
import CFSG.Adapters.LinearCatalogStated

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Foote.E27 CFSG.AGLEmbedding TauCeti
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem statedClassicalModel_typeA' {G : Type} [Group G] {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.A r q).Valid) (e : G ≃* ValidLieTypeIndex.Group ⟨.A r q, hv⟩) :
    StatedClassicalModel G .PSL (r + 1) q.p q.exponent :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e

theorem false_of_typeA (h : E27Config X K R T z) (hz : z ∈ K) {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.A r q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.A r q, hv⟩)) (hp3 : q.p ≠ 3)
    (hr : (3 ≤ r ∧ 4 ≤ q.p ^ q.exponent) ∨ (4 ≤ r ∧ q.p ^ q.exponent = 2)) : False := by
  obtain ⟨e⟩ := e
  refine false_of_psl_model h hz (statedClassicalModel_typeA' hv e) hp3 ?_
  rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by omega, h2⟩
  · exact Or.inr ⟨by omega, h2⟩

end CFSG.HardMathSupport.Malle.E27Lie
