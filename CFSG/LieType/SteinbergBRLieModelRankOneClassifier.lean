module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.LieType.SteinbergBR.RankOneClassifier

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem exists_elementaryAbelian_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {p : ℕ} [Fact p.Prime] (r : ℕ)
    (h : ∃ A : Subgroup X, CFSG.IsElementaryAbelian p A ∧ Nat.card A = p ^ r) :
    ∃ A : Subgroup Y, CFSG.IsElementaryAbelian p A ∧ Nat.card A = p ^ r := by
  obtain ⟨A, hA, hc⟩ := h
  exact ⟨A.map e.toMonoidHom, CFSG.IsElementaryAbelian.map (A := A) e.toMonoidHom,
    by rw [Subgroup.card_map_of_injective e.injective, hc]⟩

theorem pRank_eq_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (p : ℕ)
    [Fact p.Prime] : CFSG.pRank p X = CFSG.pRank p Y := by
  unfold CFSG.pRank
  congr 1
  ext r
  exact ⟨exists_elementaryAbelian_of_mulEquiv e r, exists_elementaryAbelian_of_mulEquiv e.symm r⟩

end CFSG.LieType.SteinbergBR.RankOneClassifier

