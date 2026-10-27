module

public import CFSG.GH74.E2.KTables
public import CFSG.GH74.KGroups.Sz8
public import CFSG.GH74.KGroups.Cover

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG CFSG.Blueprint
open CFSG.GH74.E2 hiding Hyp

theorem false_of_solvable_quasisimple {K : Type} [Group K] {L : Subgroup K}
    (hq : CFSG.IsQuasisimple ↥L) (hs : Group.IsSolvable ↥L) : False :=
  CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hq hs

theorem pumpUpData2 :
    PumpUpData2 where
  shape_of_fixed := by
    intro K _ _ hK α hα2 hα1 L hL hLq
    rcases k0Shape_split hK with hc | hu
    · exact absurd hLq (covered_fixed_not_quasisimple hc α hα2 hα1 L hL)
    · rcases hu with hSz | h2M | h2S
      · exfalso
        obtain ⟨e⟩ := CFSG.GH74.KGroups.Sz8.equiv_of_lieModel hSz
        exact false_of_solvable_quasisimple hLq
          (CFSG.GH74.KGroups.Sz8.fixed_solvable e α hα2 hα1 L hL)
      · exact h2M
      · exfalso
        obtain ⟨hqK, -, hmod⟩ := h2S
        obtain ⟨e⟩ := CFSG.GH74.KGroups.Sz8.equiv_of_lieModel hmod
        refine CFSG.GH74.KGroups.cover_pumpup_solvable hqK.1 ?_ α hα2 hα1 L hL hLq.1 ?_
        · intro β hβ2 hβ1 Lb hLb
          exact CFSG.GH74.KGroups.Sz8.fixed_solvable e β hβ2 hβ1 Lb hLb
        · intro hcomm
          obtain ⟨-, -, ⟨a, b, hab⟩⟩ := hLq
          obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
          obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
          exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm a' b'])

end CFSG.GH74.AS16.E2
