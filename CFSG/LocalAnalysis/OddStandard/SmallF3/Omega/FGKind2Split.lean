module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGKind2Layer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qS59Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem fg_kind2_split_of_schur (hS : Asc82SchurU43) : Asc82Kind2Split := by
  intro G _ _ L hL t ht ht2 s hs2 hα B hB hB5 htB
  obtain ⟨α, V, _, _, _, Q, hQ, e, x, hdim, hsgn, hind, hxt⟩ := hα
  obtain ⟨φ, hφ, he⟩ := t5_cover_of_model hS hL hdim hsgn e
  obtain ⟨y, hyx, hy1, g, hgg, hgty, hgy⟩ := hxt
  have hxg : x = projOrthToProjSim Q (toProj Q g) := by rw [← hyx, ← hgy]
  have hact : CoverAct L φ s (orthToSim Q g) :=
    t5_coverAct_of_inducesViaP hL hφ he hind (by rw [hxg]; exact (projOrthToProjSim_toProj g).symm)
  have hs2' : s * s = 1 := by rw [← pow_two, ← hs2]; exact pow_orderOf_eq_one s
  have hB2 : ∀ b ∈ B, b * b = 1 := fun b hb => by
    have h := hB5.1.2 b hb
    rwa [pow_two] at h
  exact fg_kind2_split_of_cover hL hφ hs2' hgg hgty hact ht ht2 hB hB2 htB

end CFSG.OddStandard.SmallF3.Omega
