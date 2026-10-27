module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTGeneric
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTSolvable
import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
import CFSG.RankThree.PartOne.CTP.SeitzExcModels

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.Sporadic.Schreier.Tits
open CFSG.HardMathSupport.Dickson.SuzukiReeB (exists_eq_conj_of_mem_range fixSubgroup_conj)

section Tits

set_option linter.unusedSectionVars false


theorem isSolvable_fixSubgroup_tits (hv : TauCeti.LieTypeIndex.tits.Valid) {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {β : MulAut S} (hβ : β ^ p = 1) (hβ1 : β ≠ 1) :
    Group.IsSolvable ↥(fixSubgroup β) := by
  obtain ⟨e⟩ :=
    titsModelEquiv S 2 1 (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits (S := S) ⟨hv, he⟩)
  have hZ : Subgroup.center titsD = ⊥ := by
    rw [← Subgroup.map_center_eq e, b3Lie_center_eq_bot hnc, Subgroup.map_bot]
  have hβ' : MulAut.congr e β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1' : MulAut.congr e β ≠ 1 := fun h => hβ1 ((MulAut.congr e).map_eq_one_iff.mp h)
  have hmem : MulAut.congr e β ∈ (MulAut.conj : titsD →* MulAut titsD).range :=
    titsD_mem_inner_of_pow_eq_one hp hp2 hβ'
  obtain ⟨x, hx, hxp, hx1⟩ := exists_eq_conj_of_mem_range hZ hmem hβ' hβ1'
  refine SRT.isSolvable_fixSubgroup_of_congr e β ?_
  rw [hx, fixSubgroup_conj]
  exact isSolvable_centralizer_titsD hp hp2 hxp hx1

theorem srtOut_tits (hv : TauCeti.LieTypeIndex.tits.Valid) {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {β : MulAut S} (hβ : β ^ p = 1) (hβ1 : β ≠ 1) : SRTOut 2 β :=
  srtOut_of_isSolvable 2 β (isSolvable_fixSubgroup_tits hv hnc he hp hp2 hβ hβ1)

end Tits

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
