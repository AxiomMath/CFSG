module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsB1Group
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsB1Comm
public import CFSG.Sporadic.Schreier.RuAutInner

public noncomputable section

namespace CFSG.EvenSporadicStandard.RuStd

open Subgroup CFSG.Sporadic.RuSchreier
open scoped commutatorElement

@[expose] def ruRepZ15 : ruP := ⟨ruRepZ 15, mem_ruP_of_mem_ruZP (ruRepZ_mem 15)⟩

theorem card_centralizer_ruA0' :
    Nat.card (centralizer ({ruA0'} : Set ruP)) = 116480 := by
  rw [card_centralizer_subtype]
  show Nat.card (ruP ⊓ Subgroup.centralizer {ruA0} : Subgroup _) = _
  rw [ruCentralizer_a, card_ruL]

theorem card_centralizer_ruRepZ15 :
    Nat.card (centralizer ({ruRepZ15} : Set ruP)) = 245760 := by
  rw [card_centralizer_subtype]
  show Nat.card (ruP ⊓ Subgroup.centralizer {ruRepZ 15} : Subgroup _) = _
  have h := ncard_conjSet_mul_card ruP (ruRepZ 15)
  rw [conjSet_eq_of_mem (ruRepZ_mem 15)] at h
  have h1 : (conjSet ruP ruZ).ncard = 593775 := ncard_ruZP
  rw [h1, card_ruP] at h
  omega

theorem card_centralizer_inf_pair :
    Nat.card ↥(centralizer ({ruRepZ15} : Set ruP) ⊓ centralizer ({ruA0'} : Set ruP)) = 256 := by
  rw [card_centralizer_inf_subtype]
  show Nat.card (ruP ⊓ Subgroup.centralizer {ruRepZ 15} ⊓ Subgroup.centralizer {ruA0} :
    Subgroup _) = _
  rw [inf_right_comm, ruCentralizer_a, card_ruL_centralizer_rep (by norm_num : 15 < 19)]
  rfl

theorem ruP_pair :
    ∃ u a : ruP, orderOf u = 2 ∧ Nat.card (centralizer ({u} : Set ruP)) = 116480 ∧
      orderOf a = 2 ∧ Nat.card (centralizer ({a} : Set ruP)) = 245760 ∧ a * u = u * a ∧
      a ∈ derivedCentralizer u ∧
      Nat.card ↥(centralizer ({a} : Set ruP) ⊓ centralizer ({u} : Set ruP)) = 256 := by
  obtain ⟨g, hg, h, hh, hgh⟩ := ruRepZ15_eq_commutator
  have hcomm : ∀ x ∈ ruL, x * ruA0 = ruA0 * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.1 (ruL_le_centralizer hx).2
  have hmem : ruRepZ 15 ∈ ruL := hgh ▸ ruL.mul_mem (ruL.mul_mem (ruL.mul_mem hg hh)
    (ruL.inv_mem hg)) (ruL.inv_mem hh)
  have hgc : (⟨g, ruL_le hg⟩ : ruP) ∈ centralizer ({ruA0'} : Set ruP) :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext (hcomm g hg))
  have hhc : (⟨h, ruL_le hh⟩ : ruP) ∈ centralizer ({ruA0'} : Set ruP) :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext (hcomm h hh))
  refine ⟨ruA0', ruRepZ15, ?_, card_centralizer_ruA0', ?_, card_centralizer_ruRepZ15,
    Subtype.ext (hcomm _ hmem), ?_, card_centralizer_inf_pair⟩
  · rw [← Subgroup.orderOf_coe]
    exact orderOf_ruA0
  · rw [← Subgroup.orderOf_coe]
    exact orderOf_of_mem_ruZP (ruRepZ_mem 15)
  · have := commutatorElement_mem_derivedCentralizer hgc hhc
    rwa [show ⁅(⟨g, ruL_le hg⟩ : ruP), ⟨h, ruL_le hh⟩⁆ = ruRepZ15 from Subtype.ext hgh] at this

end CFSG.EvenSporadicStandard.RuStd
