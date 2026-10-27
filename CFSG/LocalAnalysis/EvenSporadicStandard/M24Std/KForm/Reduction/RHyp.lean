module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.LemmaR.Hyp
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import CFSG.Mathlib.GroupTheory.PermCommute

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Reduction

open Subgroup CFSG.EvenSporadicStandard.HSStd.InvCent

theorem rhyp_top {A : Type*} [Group A] [IsSimpleGroup A] (hnab : ∃ a b : A, a * b ≠ b * a) :
    RHyp A (⊤ : Subgroup A) where
  normal := inferInstance
  simple := MulEquiv.isSimpleGroup (Subgroup.topEquiv : ↥(⊤ : Subgroup A) ≃* A)
  nonab := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨a, mem_top a, b, mem_top b, hab⟩
  min := fun N hN hNne => by
    haveI : N.Normal := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact absurd h hNne
    · exact h.ge
  center := fun x hx => by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center A) with h | h
    · have h1 : x ∈ Subgroup.center A := Subgroup.mem_center_iff.2 hx
      rwa [h, Subgroup.mem_bot] at h1
    · obtain ⟨a, b, hab⟩ := hnab
      have hb : b ∈ Subgroup.center A := by rw [h]; exact mem_top b
      exact absurd (Subgroup.mem_center_iff.1 hb a) hab

theorem rhyp_alt8 :
    RHyp (alternatingGroup (Fin 8)) (⊤ : Subgroup (alternatingGroup (Fin 8))) := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  refine rhyp_top ?_
  by_contra hcon
  have hcom : ∀ a b : alternatingGroup (Fin 8), a * b = b * a := by
    intro a b
    by_contra h
    exact hcon ⟨a, b, h⟩
  have hnc : ¬ IsMulCommutative (alternatingGroup (Fin 8)) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three]
    simp
  exact hnc ⟨⟨hcom⟩⟩

theorem even_natCard_top_alt8 :
    Even (Nat.card ↥(⊤ : Subgroup (alternatingGroup (Fin 8)))) := by
  rw [Subgroup.card_top, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem rhyp_perm6 : RHyp (Equiv.Perm (Fin 6)) (alternatingGroup (Fin 6)) where
  normal := inferInstance
  simple := alternatingGroup.isSimpleGroup (by simp)
  nonab := by
    refine ⟨Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2, ?_,
      Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 3, ?_, ?_⟩
    · exact Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
        (Equiv.Perm.swap_isSwap_iff.mpr (by decide))
        (Equiv.Perm.swap_isSwap_iff.mpr (by decide))
    · exact Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
        (Equiv.Perm.swap_isSwap_iff.mpr (by decide))
        (Equiv.Perm.swap_isSwap_iff.mpr (by decide))
    · decide
  min := fun N hN hNne => by
    haveI : N.Normal := hN
    exact Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 6) (by simp)
      ((Subgroup.nontrivial_iff_ne_bot N).mpr hNne)
  center := fun x h => CFSG.perm_eq_one_of_forall_commute (by simp) fun y => (h y).symm

theorem even_natCard_alt6 : Even (Nat.card ↥(alternatingGroup (Fin 6))) := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

end CFSG.EvenSporadicStandard.M24Std.KForm.Reduction
