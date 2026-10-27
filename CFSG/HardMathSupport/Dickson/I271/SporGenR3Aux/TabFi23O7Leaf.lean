module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23O7Om
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Leaf
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.ClassicalBridgeB
import CFSG.Adapters.StatedSmallProjOrders

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.RankThree.PartOne.N143.O7 (Om modelEquiv)

private theorem card_zmod_three' : Nat.card (ZMod 3) = 3 := by
  rw [Nat.card_eq_fintype_card, ZMod.card]

theorem tabFi23_isChevSimple_om : IsChevSimple 3 ↥Om := by
  have h := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_statedProj_odd_gen
    (K := ZMod 3) 3 le_rfl (by rw [ZMod.ringChar_zmod_n]; norm_num)
  rw [ZMod.ringChar_zmod_n] at h
  exact isChevSimple_of_mulEquiv (modelEquiv card_zmod_three') h

theorem tabFi23_leafType_of_equiv_om {T : Type} [Group T] (e : T ≃* ↥Om) : LeafType 3 T := by
  have hcard : Nat.card T = 4585351680 := tabFi23_card_of_equiv_om e
  refine Or.inl ⟨isChevSimple_of_mulEquiv e.symm tabFi23_isChevSimple_om, ?_, ?_⟩
  · intro h
    obtain ⟨F, _, _, hF, ⟨e'⟩⟩ := h
    have h2 : Nat.card (StatedProj (StatedSL 2 F)) = 9828 := by
      rw [CFSG.Open.StatedAPI.card_statedProj_statedSL_two_of_odd (by rw [hF]; decide), hF]
      norm_num
    rw [Nat.card_congr e'.toEquiv, h2] at hcard
    omega
  · rintro ⟨f⟩
    rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup] at hcard
    simp [Nat.factorial] at hcard

end CFSG.HardMathSupport.Dickson.I271
