module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofCoverLie
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofCore
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofAutSL
import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Subgroup CFSG.LocalAnalysis.ComponentInitial

theorem outDiag_of_linear {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hGA : CFSG.Open.GriessAllModelsStatement) {L : Type} [Group L] [Finite L]
    (hL : CFSG.Open.IsQuasisimple L) (hZne : center L ≠ ⊥) (hZp : IsPGroup p (center L))
    {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    (e : L ⧸ center L ≃* LinearFlag.projectiveSL n K) (α δ : MulAut L) (a b : ℕ)
    (hδp : δ ^ p = 1) (hδ : δ ∉ (MulAut.conj : L →* MulAut L).range)
    (hαδ : α * δ * α⁻¹ = δ ^ b) (hαc : ∀ c ∈ center L, c ^ p = 1 → α c = c ^ a) :
    (a : ZMod p) = b ∨ (b : ZMod p) = 1 := by
  obtain ⟨φ, hφ, hφπ⟩ := exists_cover_linear hp hp5 hGA hL hZp hn e
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) K) :=
    LinearGroups.special_linear_isPerfect (by omega) (Or.inl hn)
  exact outDiag_core hp hL hZne hZp hperf (LinearFlag.proj n K) e φ hφπ hφ
    (LinearFlag.conjAut n K) (Matrix.GeneralLinearGroup.det (n := Fin n) (R := K))
    (l212in_comm_mem_range_conjAut hn) (l212in_conjAut_eq_one hn) l212in_conjAut_mem_inner
    (l212in_lift_linear hn) α δ a b hδp hδ hαδ hαc

end CFSG.LocalAnalysis.RankFourTheoremC
