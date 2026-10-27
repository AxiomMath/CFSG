module

public import Mathlib.GroupTheory.Frattini
import CFSG.FeitThompson.Local.CriticalEnlargementCharacteristic
import CFSG.FeitThompson.Foundations.MinimalNormalInFittingCenter
import CFSG.FeitThompson.Local.CriticalPrimeTorsionDetectsAutomorphisms

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {p n : ℕ} {P : Type*} [Group P]

structure IsThompsonCritical (C : Subgroup P) : Prop where
  characteristic : C.Characteristic
  frattini_le_center : frattini ↥C ≤ center ↥C
  commutator_top_le_center : ⁅(⊤ : Subgroup P), C⁆ ≤ (center ↥C).map C.subtype
  centralizer_eq_center : centralizer (C : Set P) = (center ↥C).map C.subtype

theorem commutator_self_le_of_commutator_top_le {C N : Subgroup P}
    (hC : ⁅(⊤ : Subgroup P), C⁆ ≤ N) : ⁅C, C⁆ ≤ N :=
  (Subgroup.commutator_mono le_top le_rfl).trans hC

theorem IsThompsonCritical.commutator_self_le_center {C : Subgroup P}
    (hC : IsThompsonCritical C) : ⁅C, C⁆ ≤ (center ↥C).map C.subtype :=
  commutator_self_le_of_commutator_top_le hC.commutator_top_le_center

theorem center_bot_eq_top : center ↥(⊥ : Subgroup P) = ⊤ := by
  refine eq_top_iff.2 fun x _ => Subgroup.mem_center_iff.2 fun g => ?_
  have hg : g = 1 := Subtype.ext (Subgroup.mem_bot.1 g.2)
  simp [hg]

theorem ne_bot_of_centralizer_eq_map_center [Nontrivial P] {C : Subgroup P}
    (hC : centralizer (C : Set P) = (center ↥C).map C.subtype) : C ≠ ⊥ := by
  rintro rfl
  obtain ⟨x, hx⟩ := exists_ne (1 : P)
  have h1 : x ∈ centralizer ((⊥ : Subgroup P) : Set P) :=
    Subgroup.mem_centralizer_iff.2 fun g hg => by simp [Subgroup.mem_bot.1 hg]
  rw [hC, map_center_subtype_eq_inf_centralizer, bot_inf_eq, Subgroup.mem_bot] at h1
  exact hx h1

theorem IsThompsonCritical.ne_bot [Nontrivial P] {C : Subgroup P} (hC : IsThompsonCritical C) :
    C ≠ ⊥ :=
  ne_bot_of_centralizer_eq_map_center hC.centralizer_eq_center

theorem isThompsonCritical_bot [Subsingleton P] : IsThompsonCritical (⊥ : Subgroup P) where
  characteristic := inferInstance
  frattini_le_center := by rw [center_bot_eq_top]; exact le_top
  commutator_top_le_center := by rw [Subgroup.commutator_bot_right]; exact bot_le
  centralizer_eq_center := Subsingleton.elim _ _

theorem IsThompsonCritical.centralizer_le {C : Subgroup P} (hC : IsThompsonCritical C) :
    centralizer (C : Set P) ≤ C :=
  (centralizer_eq_map_center_iff_centralizer_le C).1 hC.centralizer_eq_center

theorem exists_isThompsonCritical (hp : p.Prime) (hP : Nat.card P = p ^ n) :
    ∃ C : Subgroup P, IsThompsonCritical C := by
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; exact pow_ne_zero _ hp.pos.ne')
  set S : Set (Subgroup P) := {K | K.Characteristic ∧ frattini ↥K ≤ center ↥K ∧
    ⁅(⊤ : Subgroup P), K⁆ ≤ (center ↥K).map K.subtype} with hS
  have hbot : (⊥ : Subgroup P) ∈ S := by
    refine ⟨inferInstance, ?_, ?_⟩
    · rw [center_bot_eq_top]; exact le_top
    · rw [Subgroup.commutator_bot_right]; exact bot_le
  obtain ⟨K, ⟨hKS, hKmax⟩⟩ := S.toFinite.exists_maximal ⟨_, hbot⟩
  obtain ⟨hKchar, hKΦ, hKP⟩ := hKS
  have := hKchar
  refine ⟨K, hKchar, hKΦ, hKP, le_antisymm ?_ ?_⟩
  · by_contra hne
    have hlt : (center ↥K).map K.subtype < centralizer (K : Set P) :=
      lt_of_le_of_ne (by rw [map_center_subtype_eq_inf_centralizer]; exact inf_le_right)
        fun h => hne (le_of_eq h.symm)
    obtain ⟨L, hLchar, hKL, hLΦ, hLP⟩ := exists_characteristic_gt p K hp hP hKΦ hKP hlt
    exact hKL.not_ge (hKmax ⟨hLchar, hLΦ, hLP⟩ hKL.le)
  · rw [map_center_subtype_eq_inf_centralizer]; exact inf_le_right

theorem exists_characteristic_critical (hp : p.Prime) (hP : Nat.card P = p ^ n) :
    ∃ C : Subgroup P, C.Characteristic ∧ frattini ↥C ≤ center ↥C ∧
      ⁅(⊤ : Subgroup P), C⁆ ≤ (center ↥C).map C.subtype ∧
      centralizer (C : Set P) = (center ↥C).map C.subtype ∧
      (Nontrivial P → C ≠ ⊥ ∧ ⁅C, C⁆ ≤ (center ↥C).map C.subtype) := by
  obtain ⟨C, hC⟩ := exists_isThompsonCritical hp hP
  exact ⟨C, hC.characteristic, hC.frattini_le_center, hC.commutator_top_le_center,
    hC.centralizer_eq_center, fun _ => ⟨hC.ne_bot, hC.commutator_self_le_center⟩⟩

end

end CFSG.FeitThompson
