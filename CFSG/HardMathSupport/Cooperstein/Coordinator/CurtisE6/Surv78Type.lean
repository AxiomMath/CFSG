module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Surv78Simple
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.MinRep

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.Min

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem

structure AdjTop (τ : Tag) (θ : Fin τ.rank → ℤ) (n : Fin τ.rank) : Prop where
  root : IsRoot τ θ
  hyp : AdjHyp τ θ
  not_succ : ∀ i : Fin τ.rank, ¬ IsRoot τ (θ + Pi.single i 1)
  ne_single : ∀ i : Fin τ.rank, θ ≠ Pi.single i 1
  ne_neg : ∀ i : Fin τ.rank, θ ≠ -Pi.single i 1
  reflect_ne : ∀ i : Fin τ.rank, i ≠ n → reflect τ i θ = θ
  reflect_node : reflect τ n θ = θ - Pi.single n 1
  root_sub : IsRoot τ (θ - Pi.single n 1)
  sub_ne_single : θ - Pi.single n 1 ≠ Pi.single n 1
  sub_ne_neg : θ - Pi.single n 1 ≠ -Pi.single n 1
  weight : ∀ s : Fin τ.rank, ∑ j, τ.cartan s j * θ j = if s = n then 1 else 0

variable {τ : Tag} {θ : Fin τ.rank → ℤ} {n : Fin τ.rank} {K : Type} [Field K] [CharP K 2]

theorem adjRep_dC_theta (T : AdjTop τ θ n) (s : Fin τ.rank) (t : Kˣ) :
    adjRep τ K (dC τ K s t) (rootVec τ K θ) =
      ((t ^ (if s = n then (1 : ℤ) else 0) : Kˣ) : K) • rootVec τ K θ := by
  rw [adjRep_apply]
  change (torusElt τ K s t : Module.End K (RootModule τ K)) (rootVec τ K θ) = _
  rw [torusElt_rootVec s t T.root, T.weight s]

theorem adjRep_xC_nC_apply (i : Fin τ.rank) (c : K) (v : RootModule τ K) :
    adjRep τ K (xC τ K i c * nC τ K i) v =
      xOp τ K i c ((weylElt τ K i 1 : Module.End K (RootModule τ K)) v) := by
  rw [map_mul, Module.End.mul_apply, adjRep_xC, adjRep_nC]

theorem adj_xn_theta_of_ne (T : AdjTop τ θ n) {s : Fin τ.rank} (hs : s ≠ n) (c : K) :
    adjRep τ K (xC τ K s c * nC τ K s) (rootVec τ K θ) = rootVec τ K θ := by
  rw [adjRep_xC_nC_apply, weylElt_one_rootVec' s T.root, T.reflect_ne s hs]
  exact xOp_rootVec_of_up_zero T.hyp s c T.root (T.ne_single s) (T.ne_neg s) (T.not_succ s)

theorem adj_xn_theta_node (T : AdjTop τ θ n) (c : K) :
    adjRep τ K (xC τ K n c * nC τ K n) (rootVec τ K θ) =
      rootVec τ K (θ - Pi.single n 1) + c • rootVec τ K θ := by
  rw [adjRep_xC_nC_apply, weylElt_one_rootVec' n T.root, T.reflect_node,
    xOp_rootVec_of_up_one T.hyp n c T.root_sub T.sub_ne_single T.sub_ne_neg
      (by rw [sub_add_cancel]; exact T.root), sub_add_cancel]

theorem adj_heckeSum_of_ne [Fintype K] (T : AdjTop τ θ n) {s : Fin τ.rank} (hs : s ≠ n) :
    ∑ c : K, adjRep τ K (xC τ K s c * nC τ K s) (rootVec τ K θ) = 0 := by
  simp only [adj_xn_theta_of_ne T hs, Finset.sum_const, Finset.card_univ]
  exact card_smul_eq_zero' K _

theorem adj_heckeSum_node [Fintype K] (T : AdjTop τ θ n) :
    ∑ c : K, adjRep τ K (xC τ K n c * nC τ K n) (rootVec τ K θ) =
      (∑ c : K, c) • rootVec τ K θ := by
  simp only [adj_xn_theta_node T, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
  rw [card_smul_eq_zero' K, zero_add, Finset.sum_smul]

end CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.Min
