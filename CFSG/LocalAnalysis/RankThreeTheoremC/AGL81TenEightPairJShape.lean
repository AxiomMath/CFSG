module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenEight

open CFSG.AGLEmbedding CFSG.QuasithinUnique

@[expose] def U42Facts (Y : Type) [Group Y] : Prop :=
  CFSG.AGLEmbedding.BlockCyc.HasE9 Y ∧
    ∀ (Z : Type) [Group Z] [Finite Z], CFSG.Open.IsQuasisimple Z →
      Odd (Nat.card (Subgroup.center Z)) → Nonempty (Z ⧸ Subgroup.center Z ≃* Y) →
        Subgroup.center Z = ⊥

@[expose] def KFactThreeFourPairJShape : Prop :=
  ∀ (p : ℕ) (iK iJ : TauCeti.CFSGIndex), TenThirteen.IsThreeFourPair p iK iJ →
  ∀ (Y : Type) [Group Y] [Finite Y], Nonempty (Y ≃* iJ.Group) →
    (IsSimpleGroup Y ∧ ∃ a b : Y, a * b ≠ b * a) ∧
    (∀ N : ℕ, 6 ≤ N → IsEmpty (Y ≃* alternatingGroup (Fin N))) ∧
    (IsOrthogonalTwo Y → Nonempty (Y ≃* alternatingGroup (Fin 5)) ∨ U42Facts Y) ∧
    (IsClassicalTwoOrG2 Y → ∀ T J : Subgroup Y, IsSylowTwoOf T ⊤ →
      Subgroup.normalizer (T : Set Y) ≤ J → J ≠ Subgroup.normalizer (T : Set Y) → J ≠ ⊤ →
        U42Facts Y)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenEight
