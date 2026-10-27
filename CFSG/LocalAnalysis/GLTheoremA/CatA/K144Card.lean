module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144Main
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieEnd
import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K144

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup LieOrderBridge)

theorem card_ge_of_catalog (hB : LieOrderBridge) {X : Type} [Group X] [Finite X]
    (h : catalogIs X I144Cat) : 25920 ≤ Nat.card X := by
  obtain ⟨i, hi, he⟩ := h
  change S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i at hi
  rcases hi with h4 | h5 | h6
  · obtain ⟨q, hv, hq, ⟨e⟩⟩ := CatB.lieIndex_isU4two ⟨i, h4, he⟩
    have hcard := hB ⟨.twistedA 3 q, hv⟩ X ⟨e⟩
    change Nat.card X = orderTwistedA 3 q.card at hcard
    rw [hq] at hcard
    rw [hcard]
    decide
  · obtain ⟨q, hv, hq, ⟨e⟩⟩ := CatB.lieIndex_isU5two ⟨i, h5, he⟩
    have hcard := hB ⟨.twistedA 4 q, hv⟩ X ⟨e⟩
    change Nat.card X = orderTwistedA 4 q.card at hcard
    rw [hq] at hcard
    rw [hcard]
    decide
  · obtain ⟨q, hv, hq, ⟨e⟩⟩ := CatB.lieIndex_isSp6two ⟨i, h6, he⟩
    have hcard := hB ⟨.B 3 q, hv⟩ X ⟨e⟩
    change Nat.card X = orderBC 3 q.card at hcard
    rw [hq] at hcard
    rw [hcard]
    decide

theorem card_pSimple_le_fix {S : Type} [Group S] [Finite S] {β : MulAut S} {Jb : Subgroup S}
    (hJ : GLAPComponent 3 (fixSubgroup β) Jb) :
    Nat.card (PSimple 3 Jb) ≤ Nat.card ↥(fixSubgroup β) := by
  have h1 : Nat.card (PSimple 3 Jb) ≤ Nat.card ↥Jb :=
    Nat.card_le_card_of_surjective
      (fun x : ↥Jb => (QuotientGroup.mk (QuotientGroup.mk x : PQuot 3 Jb) : PSimple 3 Jb))
      (QuotientGroup.mk_surjective.comp QuotientGroup.mk_surjective)
  exact h1.trans (Subgroup.card_le_of_le hJ.1)

end CFSG.LocalAnalysis.GLTheoremA.K144
