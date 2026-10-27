module

public import CFSG.GH74.GLS.C3.Layer1.Th2Struct
public import CFSG.GH74.GLS.C3.Layer1.St1Thm7

public section

namespace CFSG.GH74.GLS.Th2

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS

variable {G : Type} [Group G]

theorem isElementaryAbelian_zpowers_of_orderOf_two {z : G} (hz : orderOf z = 2) :
    CFSG.IsElementaryAbelian 2 ↥(zpowers z) := by
  have : z ^ 2 = 1 := by rw [pow_two]; exact mul_self_eq_one_of_orderOf_eq_two hz
  exact CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one this

theorem pRank_zpowers_of_orderOf_two [Finite G] {z : G} (hz : orderOf z = 2) :
    pRank 2 ↥(zpowers z) = 1 := by
  have hc : Nat.card ↥(zpowers z) = 2 := by rw [Nat.card_zpowers]; exact hz
  have h2 := C3.Layer1.Back.card_eq_two_pow_pRank (isElementaryAbelian_zpowers_of_orderOf_two hz)
  rw [hc] at h2
  have : (2 : ℕ) ^ 1 = 2 ^ pRank 2 ↥(zpowers z) := by simpa using h2
  exact (Nat.pow_right_injective le_rfl this).symm

theorem pRank_eq_of_isSylowOf [Finite G] {H Q : Subgroup G} (hQ : IsSylowOf 2 Q H) :
    pRank 2 ↥Q = pRank 2 ↥H := by
  have hle : pRank 2 ↥Q ≤ pRank 2 ↥H := C3.Layer1.Back.pRank_mono' hQ.le
  refine le_antisymm hle ?_
  obtain ⟨E, hEH, hEel, hErk⟩ := exists_elemAbelian_pRank H
  obtain ⟨g, -, hgE⟩ := Th2.exists_cj_le_of_isSylowOf hQ hEH (CFSG.IsElementaryAbelian.isPGroup 2 _)
  rw [← hErk, ← pRank_cj g E]
  exact C3.Layer1.Back.pRank_mono' hgE

theorem twoPartCard_eq_card_of_isSylowOf [Finite G] {H Q : Subgroup G} (hQ : IsSylowOf 2 Q H) :
    twoPartCard H = Nat.card ↥Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [hQ.card_eq]
  rfl

theorem U2Succ_congr_right {H J J' : Type} [Group H] [Group J] [Group J'] (e : J ≃* J')
    (h : U2Succ H J) : U2Succ H J' := by
  obtain ⟨hH, hJ, hcases⟩ := h
  have hC : InC2 J ↔ InC2 J' :=
    ⟨CFSG.GH74.E2.inC2_of_mulEquiv e, CFSG.GH74.E2.inC2_of_mulEquiv e.symm⟩
  have hA7 : Nonempty (J ≃* alternatingGroup (Fin 7)) ↔
      Nonempty (J' ≃* alternatingGroup (Fin 7)) :=
    ⟨fun ⟨f⟩ => ⟨e.symm.trans f⟩, fun ⟨f⟩ => ⟨e.trans f⟩⟩
  have hcard : Nat.card J = Nat.card J' := Nat.card_congr e.toEquiv
  refine ⟨hH, inU2_of_mulEquiv e hJ, ?_⟩
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, fun hf => h2 (hA7.2 hf)⟩
  · exact Or.inr (Or.inl ⟨h1, hC.1 h2⟩)
  · refine Or.inr (Or.inr ⟨?_, hcard ▸ h2⟩)
    rcases h1 with ⟨ha, hb⟩ | ⟨⟨ha, hb⟩, hc, hd⟩
    · exact Or.inl ⟨ha, hC.1 hb⟩
    · exact Or.inr ⟨⟨ha, hb⟩, fun hf => hc (hC.2 hf), fun hf => hd (hA7.2 hf)⟩

end CFSG.GH74.GLS.Th2

