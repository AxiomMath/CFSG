module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D4FCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)

theorem kd26bcD4Char3Ne_holds : KD26bcD4Char3Ne := by
  intro S _ _ _ _ r f hm h3 hr D hD hcard hinn
  have hf : 1 ≤ f := hm.1.2.1
  have hadm : StatedLieAdmissible .POmegaPlus 4 r (f / 3) :=
    ⟨hm.1.1, Nat.div_pos (Nat.le_of_dvd (by omega) h3) (by norm_num), le_rfl⟩
  have hne : 3 ≠ r := fun h => hr h.symm
  exact field_core hm h3 (fun K _ _ k hk hK σ hσ hσk =>
    (CFSG.LieType.SeitzGeneration.orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd
      .POmegaPlus (Or.inr (Or.inl rfl)) 4 r (f / 3) 3 hadm Nat.prime_three (by norm_num) hne
      K k hk hK σ hσ hσk).2) D hD hcard hinn

theorem kd26bcD4Char3_holds : KD26bcD4Char3 := by
  intro S _ _ _ _ r f hm h3 _ D hD hcard hinn
  have hf : 1 ≤ f := hm.1.2.1
  have hadm : StatedLieAdmissible .POmegaPlus 4 r (f / 3) :=
    ⟨hm.1.1, Nat.div_pos (Nat.le_of_dvd (by omega) h3) (by norm_num), le_rfl⟩
  exact field_core hm h3 (fun K _ _ k hk hK σ hσ hσk =>
    (orthPlus_subfield_any hadm Nat.prime_three (by norm_num) K k hk hK σ hσ hσk).2)
    D hD hcard hinn

theorem kd26bcD4_holds : KD26bcD4 :=
  kd26bcD4_of_split kd26bcD4Char3Ne_holds kd26bcD4Char3_holds

end CFSG.LocalAnalysis.GLTheoremA
