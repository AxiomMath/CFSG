module

public import CFSG.CGT.PushingUpLit.SolKNA.NCPair
public import CFSG.CGT.Timmesfeld75.Inputs214
public import CFSG.RankThree.GF2n.BenderStrongWC
import CFSG.CGT.Timmesfeld75.Core214Proof
import CFSG.CGT.Timmesfeld75.AschbacherNoPolarDischarge
public import CFSG.CGT.Timmesfeld75.NormalClosure

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n
open scoped MatrixGroups

variable {Y : Type} [Group Y] [Finite Y]

namespace NCPair

variable {T T' : Subgroup Y} (h : NCPair T T')
include h

theorem models
    (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) :
    (∀ K : Subgroup Y, K.Normal → IsPGroup 2 K → K = ⊥) ∧
      ((∃ f : ℕ, 2 ≤ f ∧ Nat.card T = 2 ^ f ∧ Nonempty (Y ≃* PSL(2, GaloisField 2 f))) ∨
        (∃ a : ℕ, 1 ≤ a ∧ Nat.card T = 2 ^ (2 * a + 1) ∧ Nonempty (Y ≃* Sz a)) ∨
        (∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ Nat.card T = 2 ∧ Nonempty (Y ≃* DihedralGroup m))) := by
  have hS := h.strongWC
  have hT0 := h.ne_bot
  obtain ⟨x, hx⟩ := h.exists_conj
  have hK : Subgroup.normalClosure (T : Set Y) = ⊤ := by
    rw [eq_top_iff, ← h.gen, hx]
    exact sup_le Subgroup.le_normalClosure (conjSubgroup_le_normalClosure _ _)
  have hnT : ¬ ∀ g : Y, conjSubgroup g T = T := fun hall => h.ne (by rw [hx]; exact (hall x).symm)
  have hg : ∃ g : Y, T ⊔ conjSubgroup g T = ⊤ := ⟨x, by rw [← hx]; exact h.gen⟩
  rcases lemma25_top aschbacherNoPolarInput_of_repo hS hK with hZ | hB
  · have hTT' : ¬ T' ≤ T := fun hle => h.ne (Subgroup.eq_of_le_of_card_ge hle
      (by rw [hx, CFSG.RankThree.GF2n.card_conjSubgroup])).symm
    obtain ⟨n, hn, h3, ⟨e⟩⟩ := exists_dihedral_of_zStar hS.1 h.elem' h.gen hZ hT0 hTT'
      fun a ha ha1 b hb hb1 => h.odd_orderOf_mul ha ha1 hb hb1
    exact ⟨fun K _ hK2 => eq_bot_of_dihedral hn h3 e K hK2,
      Or.inr (Or.inr ⟨n, hn, h3, card_eq_two_of_dihedral hn e.symm (isPGroup_of_strongWC hS) hT0,
        ⟨e.symm⟩⟩)⟩
  · obtain ⟨hO2, hmod⟩ := models_of_isBenderGroup hCen hU hS hT0 hnT hK hg hB
    refine ⟨hO2, ?_⟩
    rcases hmod with ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
    · exact Or.inl ⟨f, hf, card_eq_of_strongWC (.linear f hf e) hS hT0, ⟨e⟩⟩
    · have e' := e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm)
      exact Or.inr (Or.inl ⟨a, ha, card_eq_of_strongWC (.suzuki a ha e') hS hT0, ⟨e⟩⟩)

end NCPair

end CFSG.CGT.PushingUpLit.SolKNA
