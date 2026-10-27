module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15DynkinA2Series

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.RankThree.FFModules Polynomial Module

private theorem ker_aeval_one_eq_bot {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    {f : (ZMod 2)[X]} (hf1 : f.eval 1 ≠ 0) :
    LinearMap.ker (aeval (1 : Module.End (ZMod 2) M) f) = ⊥ := by
  have h1 : f.eval 1 = 1 := by
    revert hf1
    generalize f.eval 1 = c
    revert c
    decide
  have h2 : aeval (1 : Module.End (ZMod 2) M) f = 1 := by
    rw [aeval_def, eval₂_at_one, h1, map_one]
  rw [h2, LinearMap.ker_eq_bot]
  exact Function.injective_id

theorem finrank_ker_aeval_eq_factor_of_trivial {K : Type} [Group K] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] {ρ : Representation (ZMod 2) K V} {r : ℕ}
    {Vs : Fin (r + 1) → Subrepresentation ρ} (hVs : IsCompositionSeries r Vs)
    {f h : (ZMod 2)[X]} (hcop : IsCoprime f h) {k : K} (hfh : aeval (ρ k) (f * h) = 0)
    (hf1 : f.eval 1 ≠ 0) (i₀ : Fin r)
    (htriv : ∀ i : Fin r, i ≠ i₀ → factorRep (Vs i.castSucc) (Vs i.succ) k = 1) :
    finrank (ZMod 2) (LinearMap.ker (aeval (ρ k) f)) =
      finrank (ZMod 2)
        (LinearMap.ker (aeval (factorRep (Vs i₀.castSucc) (Vs i₀.succ) k) f)) := by
  classical
  rw [DynkinA2.finrank_ker_aeval_eq_sum (fun i => (hVs.covBy i).le) hVs.zero hVs.last hcop hfh,
    Finset.sum_eq_single i₀]
  · intro i _ hi
    rw [htriv i hi, ker_aeval_one_eq_bot hf1, finrank_bot]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

end CFSG.LocalAnalysis.RankThreeUC.S15

end
