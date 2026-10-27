module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem ff_layerCent_eq_bot_of_solvable_aux (L : Subgroup G) (s : G)
    (h : Group.IsSolvable ↥(L ⊓ centralizer ({s} : Set G))) : layerCent L s = ⊥ := by
  change (CFSG.layer ↥(L ⊓ centralizer ({s} : Set G))).map
    (L ⊓ centralizer ({s} : Set G)).subtype = ⊥
  rw [ff_layer_eq_bot_of_solvable h, Subgroup.map_bot]

theorem ff_innerOn_of_mem_centralizer_aux (L : Subgroup G) {s : G}
    (h : s ∈ centralizer (L : Set G)) : InnerOn L s :=
  Subgroup.mem_sup_right h

theorem ff_dinv_not_mem_centralizer_aux (L : Subgroup G) (s : G) {k : ℕ} (hk : k < 5)
    (h : DInv L s k) : s ∉ centralizer (L : Set G) := by
  interval_cases k <;> simp only [DInv] at h
  · exact h.2.1
  · exact h.2.1
  · intro hs; exact h.1 (ff_innerOn_of_mem_centralizer_aux L hs)
  · intro hs; exact h.1 (ff_innerOn_of_mem_centralizer_aux L hs)
  · intro hs; exact h.1 (ff_innerOn_of_mem_centralizer_aux L hs)

theorem ff_dinv_excl_aux (L : Subgroup G) (s : G) {i j : ℕ} (hi : i < 5) (hj : j < 5)
    (hI : DInv L s i) (hJ : DInv L s j) : i = j := by
  interval_cases i <;> interval_cases j <;> simp only [DInv] at hI hJ
  · rfl
  · exact ((ff_isL29_ne_bot hJ.2.2.1) (ff_layerCent_eq_bot_of_solvable_aux L s hI.2.2)).elim
  · exact ((ff_isOmega5_ne_bot hJ.2.1) (ff_layerCent_eq_bot_of_solvable_aux L s hI.2.2)).elim
  · exact absurd hI.1 hJ.1
  · exact absurd hI.1 hJ.1
  · exact ((ff_isL29_ne_bot hI.2.2.1) (ff_layerCent_eq_bot_of_solvable_aux L s hJ.2.2)).elim
  · rfl
  · exact absurd hI.1 hJ.1
  · exact absurd hI.1 hJ.1
  · exact absurd hI.1 hJ.1
  · exact absurd hJ.1 hI.1
  · exact absurd hJ.1 hI.1
  · rfl
  · exact ((ff_isOmega5_ne_bot hI.2.1) (ff_layerCent_eq_bot_of_solvable_aux L s hJ.2)).elim
  · rcases hJ.2.1 with h3 | h29
    · exact absurd h3 (ff_not_isOmega5_and_isL3Eps3 hI.2.1)
    · exact absurd h29 (ff_not_isOmega5_and_isL29 hI.2.1)
  · exact absurd hJ.1 hI.1
  · exact absurd hJ.1 hI.1
  · exact ((ff_isOmega5_ne_bot hJ.2.1) (ff_layerCent_eq_bot_of_solvable_aux L s hI.2)).elim
  · rfl
  · rcases hJ.2.1 with h3 | h29
    · exact ((ff_isL3Eps3_ne_bot h3) (ff_layerCent_eq_bot_of_solvable_aux L s hI.2)).elim
    · exact ((ff_isL29_ne_bot h29) (ff_layerCent_eq_bot_of_solvable_aux L s hI.2)).elim
  · exact absurd hJ.1 hI.1
  · exact absurd hJ.1 hI.1
  · rcases hI.2.1 with h3 | h29
    · exact absurd h3 (ff_not_isOmega5_and_isL3Eps3 hJ.2.1)
    · exact absurd h29 (ff_not_isOmega5_and_isL29 hJ.2.1)
  · rcases hI.2.1 with h3 | h29
    · exact ((ff_isL3Eps3_ne_bot h3) (ff_layerCent_eq_bot_of_solvable_aux L s hJ.2)).elim
    · exact ((ff_isL29_ne_bot h29) (ff_layerCent_eq_bot_of_solvable_aux L s hJ.2)).elim
  · rfl

end CFSG.OddStandard.SmallF3.Omega
