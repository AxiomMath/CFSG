module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdFields2

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem part1_2519_of_inputs (hI : Inputs2519) : Part1_2519 := by
  intro G _ _ T M hs N t zK h i hi
  obtain ⟨Ki, KP, hsh⟩ := exists_shape hI.i32 hI.p121_3 hI.p121_5 N h hi
  by_cases hne : Ki = CFSG.conjugate Ki t
  · obtain ⟨R2, hR⟩ := ident_case2 hI h hi hsh hne
    exact ⟨Ki, KP, R2, hR⟩
  · obtain ⟨R2, hR⟩ := ident_case1 hI h hi hsh hne
    exact ⟨Ki, KP, R2, hR⟩

end CFSG.QuasithinUnique.Id2519
