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

theorem cl24_index_minus {S : Type} [Group S] [Finite S] (h : LieModel S .POmegaMinus 4 3 1)
    (H : Subgroup S) (hH : H ≠ ⊤) : 163 ≤ H.index := by
  obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ :=
    LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  have hK3 : Nat.card K = 3 := by simpa using hK
  have hE := commutator_orthogonalGroup_quadMinus (K := K) (b := b) (c := c) (n := 4)
    (by norm_num) hirr
  refine cl24_index_of_proj (coe_quadMinus 4 K b c) hE e 162 ?_ H hH
  intro X _ _ _ hX
  exact cl24_core (cl24_scalar_of_card_three hK3)
    (nondegenerate_polarBilin_quadMinus_of_finite 4 K hirr)
    (P₁ := minusPair K b c ⟨0, by norm_num⟩) (P₂ := minusPair K b c ⟨1, by norm_num⟩)
    (P₃ := minusPair K b c ⟨2, by norm_num⟩)
    (minusPair_orth (by simp [Fin.ext_iff])) (minusPair_orth (by simp [Fin.ext_iff]))
    (minusPair_orth (by simp [Fin.ext_iff])) hX 162 (fun a => cl24_shell_minus hK3 b c a)

end CFSG.OddStandard.SmallF3.HypA2Leaves
