module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovCfg
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95XSolv
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
open scoped MatrixGroups

theorem ivk93cov_l2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk93CovEmpty (fun X _ => LieModel X .PSL 2 p f) := by
  intro p f hp hp2 hf
  refine ivk93cov_empty_of_cfg fun J _ _ hJ x _ n B hc => ?_
  obtain ⟨k, _, _, hkcard, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hJ
  have hπ := ivk95x_isCentralQuot_of_equiv e
  obtain ⟨g, hg, hgc, -⟩ := hπ.lift_involution hc.ord
  rw [← hg] at hc
  exact hc.false_of_solvable (hπ.solvable_centralizer (ivk95x_sl2_centralizer_solvable hgc))

end CFSG.GH74.GLS.IVK.Proofs2
