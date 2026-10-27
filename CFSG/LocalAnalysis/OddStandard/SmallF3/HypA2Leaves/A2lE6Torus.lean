module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lExcE6
public import CFSG.LieType.Chevalley.E6A5CubeModel

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6A5Cube CFSG.ComponentClassification.CatLeafProof
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem a2lE6_leviA5_eq : e6LeviA5 = C2E6Std.setA := by
  ext i
  constructor
  · rintro ⟨t, rfl⟩
    exact jA_mem_setA t
  · intro h
    obtain ⟨t, rfl⟩ := C2E6Std.exists_jA_of_mem_setA h
    exact ⟨t, rfl⟩

theorem a2lE6_subsystemGroup_eq {K : Type} [Field K] :
    subsystemGroup .E6 K e6LeviA5 = groupA K := by
  rw [a2lE6_leviA5_eq]

section Action

variable {K : Type} [Field K]

theorem a2lE6_da_mem_groupA :
    rootDiagUnit .E6 (bitsTuple (K := K) e6BitsA5) ∈ groupA K := by
  rw [← a2lE6_subsystemGroup_eq]
  exact a2l_rootDiagUnit_e6BitsA5_mem

theorem a2lE6_rootChar_bitsA5 (α : Fin (Tag.rank .E6) → ℤ) :
    rootChar (bitsTuple (K := K) e6BitsA5) α = (-1 : Kˣ) ^ α (e6Node 1) := by
  rw [rootChar, Finset.prod_eq_single (e6Node 1)]
  · simp [bitsTuple, show e6BitsA5 (e6Node 1) = true from by decide]
  · intro j _ hj
    simp [bitsTuple, e6BitsA5_eq_false j hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem a2lE6_da_apply_vecA (j : Fin 20) :
    ((rootDiagUnit .E6 (bitsTuple (K := K) e6BitsA5) : ModGL .E6 K) :
        Module.End K (RootModule .E6 K)) (vecA K j) = -vecA K j := by
  change rootDiag (bitsTuple (K := K) e6BitsA5) (rootVec Tag.E6 K (C2E6Std.rootA j)) = _
  rw [rootDiag_rootVec _ (C2E6Std.isRoot_rootA j), a2lE6_rootChar_bitsA5,
    show C2E6Std.rootA j (e6Node 1) = 1 from C2E6Std.rootA_one j]
  simp [vecA]

theorem a2lE6_da_apply_moduleA {v : RootModule .E6 K} (hv : v ∈ moduleA K) :
    ((rootDiagUnit .E6 (bitsTuple (K := K) e6BitsA5) : ModGL .E6 K) :
        Module.End K (RootModule .E6 K)) v = -v := by
  rw [moduleA_eq_span] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact a2lE6_da_apply_vecA j
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, neg_add]
  | smul c x _ hx => rw [map_smul, hx, smul_neg]

end Action

end CFSG.OddStandard.SmallF3.HypA2Leaves
