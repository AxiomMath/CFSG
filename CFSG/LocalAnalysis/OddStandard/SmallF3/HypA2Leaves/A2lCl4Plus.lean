module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl4Core
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl4Shell
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl4Transport
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.LieType.Universal.Spin

theorem cl24_index_plus {S : Type} [Group S] [Finite S] (h : LieModel S .POmegaPlus 4 3 1)
    (H : Subgroup S) (hH : H ≠ ⊤) : 163 ≤ H.index := by
  obtain ⟨⟨-, -, hn⟩, K, _, _, hK, ⟨e⟩⟩ :=
    LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  have hK3 : Nat.card K = 3 := by simpa using hK
  have hE := commutator_orthogonalGroup_quadPlus (K := K) (n := 4) (by norm_num)
  refine cl24_index_of_proj (coe_quadPlus 4 K) hE e 162 ?_ H hH
  intro X _ _ _ hX
  exact cl24_core (cl24_scalar_of_card_three hK3) (nondegenerate_polarBilin_quadPlus 4 K)
    (P₁ := plusPair K 0) (P₂ := plusPair K 1) (P₃ := plusPair K 2)
    (plusPair_orth (by decide)) (plusPair_orth (by decide)) (plusPair_orth (by decide)) hX 162
    (fun a => cl24_shell_plus hK3 a)

end CFSG.OddStandard.SmallF3.HypA2Leaves
