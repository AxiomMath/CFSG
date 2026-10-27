module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KD291Constr
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt KD29Inner)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613 (IsSecOf)

theorem kd291_solvable_of_inner {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hI : KD29Inner)
    {Y : Type} [Group Y] [Finite Y]
    (L : Subgroup Y) [L.Normal] (hs : IsSimpleGroup L) (hn : ∃ a b : L, a * b ≠ b * a)
    (hc : IsCatalogGroup L) (hlu : ¬ IsLinearOrUnitaryAt p L) (hC : centralizer (L : Set Y) = ⊥)
    (hY : 3 ≤ Open.pRank p (⊤ : Subgroup Y)) {x : Y} (hxL : x ∈ L) (hx : orderOf x = p)
    (hCx : Open.pRank p (centralizer ({x} : Set Y)) ≤ 2) :
    Group.IsSolvable ↥(centralizer ({x} : Set Y)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact hp.ne_one hx.symm
  have hx5 : x ^ p = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have h := hI p hp hp5 Y L hs hn hc hlu hC hY ⟨x, hxL, hx, hCx⟩ x hxL hx1 hx5
  exact kd291_solvable_centralizer_open (by omega) hx hY hCx
    (kd291_hcon_of_layer_core hp _ h.1 h.2)

theorem kd291_not_isSecOf_of_solvable {A : Type} [Group A] (U : Subgroup A)
    (hU : Group.IsSolvable ↥U) (S : Type) [Group S] [IsSimpleGroup S]
    (hnab : ¬ ∀ a b : S, a * b = b * a) : ¬ IsSecOf U S := by
  rintro ⟨H, hHU, ψ, hψ⟩
  haveI : Group.IsSolvable ↥H := solvable_of_solvable_injective (Subgroup.inclusion_injective hHU)
  haveI : Group.IsSolvable S := Group.isSolvable_of_surjective hψ
  exact hnab (IsSimpleGroup.comm_iff_isSolvable.mpr this)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
