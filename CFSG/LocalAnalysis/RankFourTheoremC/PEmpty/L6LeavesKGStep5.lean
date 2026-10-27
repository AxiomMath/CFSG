module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGBasic
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGQ

open CFSG.Open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGB Subgroup

variable {A : Type} [Group A] [Finite A] {p : ℕ} {Kb Sb Bb Mb : Subgroup A} {z : A}

theorem normalizer_S_le (c : KQCfg A p Kb Sb Bb Mb z) : normalizer (Sb : Set A) ≤ Mb :=
  c.cover Sb le_rfl c.S_ne Subgroup.le_normalizer c.B_le_S

theorem S_le_M (c : KQCfg A p Kb Sb Bb Mb z) : Sb ≤ Mb :=
  Subgroup.le_normalizer.trans (normalizer_S_le c)

theorem B_le_M (c : KQCfg A p Kb Sb Bb Mb z) : Bb ≤ Mb :=
  c.B_le_S.trans (normalizer_S_le c)

theorem z_mem_normalizer_inf (c : KQCfg A p Kb Sb Bb Mb z) :
    z ∈ normalizer ((Sb ⊓ Kb : Subgroup A) : Set A) :=
  mem_normalizer_inf' (c.B_le_S c.z_mem_B) (c.B_le_K c.z_mem_B)

theorem false_of_bender_sylow (c : KQCfg A p Kb Sb Bb Mb z) (h2715 : KFact2715)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 (Sb ⊓ Kb) Kb) (hB : fusionIsBenderGroup ↥Kb) :
    False := by
  have hp2 : p ≠ 2 := by have := c.five_le; omega
  have key := h2715 A Kb (Sb ⊓ Kb) z p hB hT c.z_mem_K (z_mem_normalizer_inf c) c.z_order c.prime
    hp2 Mb (inf_le_left.trans c.cover_Z) (inf_le_left.trans (S_le_M c))
  exact c.not_le key

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGQ
