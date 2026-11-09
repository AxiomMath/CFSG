module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreRankDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

@[expose] def exc3core_adjE8 : List ℕ := [4, 8, 9, 22, 40, 80, 160, 320, 128]

open CFSG.HardMathSupport.Timmesfeld.LangTorus.KacMask in
theorem exc3core_extAdj_E8 : ∀ x y : Option (Fin Tag.E8.rank),
    exc3core_extAdj .E8 exc3core_thE8 x y ↔
      (exc3core_adjE8.getD (code x) 0).testBit (code y) = true := by
  decide +kernel

open CFSG.HardMathSupport.Timmesfeld.LangTorus.KacMask in
@[expose] def exc3core_noIsoB (C : Finset (Option (Fin Tag.E8.rank))) : Prop :=
  ∀ y ∈ C, C = {y} ∨ ∃ z ∈ C, (exc3core_adjE8.getD (code y) 0).testBit (code z) = true

instance exc3core_noIsoB_decidable (C : Finset (Option (Fin Tag.E8.rank))) :
    Decidable (exc3core_noIsoB C) := by
  unfold exc3core_noIsoB
  infer_instance

open CFSG.HardMathSupport.Timmesfeld.LangTorus.KacMask in
theorem exc3core_noIso_E8 (C : Finset (Option (Fin Tag.E8.rank))) :
    exc3core_noIso .E8 exc3core_thE8 C ↔ exc3core_noIsoB C := by
  unfold exc3core_noIso exc3core_noIsoB
  simp only [exc3core_extAdj_E8]

theorem exc3core_thE8_eq : exc3core_thE8 = kacThetaE8 := rfl

set_option synthInstance.maxSize 4096 in
open CFSG.HardMathSupport.Timmesfeld.LangTorus.KacMask in
theorem exc3core_rankChk_E8_m : ∀ m < 2 ^ (Tag.E8.rank + 1), (∃ y, y ∉ setOf Tag.E8.rank m) →
    exc3core_noIsoB (setOf Tag.E8.rank m) →
    exc3core_rankTabE8 (kacMaskE8.filter fun t => kacTestB Tag.E8.rank m t.1 t.2.1 t.2.2).length
      (setOf Tag.E8.rank m).card := by
  decide +kernel

theorem exc3core_rankChk_E8 : ∀ C : Finset (Option (Fin Tag.E8.rank)), (∃ y, y ∉ C) →
    exc3core_noIso .E8 exc3core_thE8 C →
      exc3core_rankTabE8 (kacCount .E8 exc3core_thE8 C) C.card := by
  refine KacMask.forall_finset (P := fun C => (∃ y, y ∉ C) →
    exc3core_noIso .E8 exc3core_thE8 C →
      exc3core_rankTabE8 (kacCount .E8 exc3core_thE8 C) C.card) fun m hm => ?_
  rw [exc3core_noIso_E8, exc3core_thE8_eq, kacCount_setOf_E8]
  exact exc3core_rankChk_E8_m m hm

end CFSG.LocalAnalysis.GLTheoremA.I167

end
