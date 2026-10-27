module

import Mathlib.Tactic.FinCases
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UD8B
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open scoped commutatorElement

variable {G : Type*} [Group G] {z g x : G}

namespace D8Rel

theorem exists_hom (h : D8Rel z g x) :
    ∃ ε : closure ({z, g} : Set G) →* ℤˣ, ε ⟨z, z_mem z g⟩ = -1 ∧ ε ⟨g, g_mem z g⟩ = 1 := by
  classical
  let W : Subgroup (closure ({z, g} : Set G)) :=
    { carrier := {q : closure ({z, g} : Set G) |
        q = 1 ∨ q = ⟨g, g_mem z g⟩ ∨ q = ⟨x, x_mem h⟩ ∨
          q = ⟨g, g_mem z g⟩ * ⟨x, x_mem h⟩}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl)
        · exact Or.inl (Subtype.ext (by simp))
        · exact Or.inr (Or.inl (Subtype.ext (by simp)))
        · exact Or.inr (Or.inr (Or.inl (Subtype.ext (by simp))))
        · exact Or.inr (Or.inr (Or.inr (Subtype.ext (by simp))))
        · exact Or.inr (Or.inl (Subtype.ext (by simp)))
        · exact Or.inl (Subtype.ext (by simpa using h.g_sq))
        · exact Or.inr (Or.inr (Or.inr (Subtype.ext (by simp))))
        · exact Or.inr (Or.inr (Or.inl (Subtype.ext
            (by simp only [Subgroup.coe_mul, Subgroup.coe_one]
                rw [← mul_assoc, h.g_sq, one_mul]))))
        · exact Or.inr (Or.inr (Or.inl (Subtype.ext (by simp))))
        · exact Or.inr (Or.inr (Or.inr (Subtype.ext (by simpa using u_x_comm_g h))))
        · exact Or.inl (Subtype.ext (by simpa using h.x_sq))
        · exact Or.inr (Or.inl (Subtype.ext
            (by simp only [Subgroup.coe_mul, Subgroup.coe_one]
                rw [← mul_assoc, u_x_comm_g h, mul_assoc, h.x_sq, mul_one])))
        · exact Or.inr (Or.inr (Or.inr (Subtype.ext (by simp))))
        · exact Or.inr (Or.inr (Or.inl (Subtype.ext
            (by simp only [Subgroup.coe_mul, Subgroup.coe_one]
                rw [mul_assoc, u_x_comm_g h, ← mul_assoc, h.g_sq, one_mul]))))
        · exact Or.inr (Or.inl (Subtype.ext
            (by simp only [Subgroup.coe_mul, Subgroup.coe_one]
                rw [mul_assoc, h.x_sq, mul_one])))
        · exact Or.inl (Subtype.ext
            (by simp only [Subgroup.coe_mul, Subgroup.coe_one]
                rw [← mul_assoc (g*x) g x, mul_assoc g x g, u_x_comm_g h,
                  ← mul_assoc g g x, h.g_sq, one_mul, h.x_sq]))
      inv_mem' := by
        rintro a (rfl | rfl | rfl | rfl)
        · exact Or.inl (Subtype.ext (by simp))
        · exact Or.inr (Or.inl (Subtype.ext
            (by simp only [Subgroup.coe_inv]; rw [inv_eq_of_mul_eq_one_right h.g_sq])))
        · exact Or.inr (Or.inr (Or.inl (Subtype.ext
            (by simp only [Subgroup.coe_inv]; rw [inv_eq_of_mul_eq_one_right h.x_sq]))))
        · exact Or.inr (Or.inr (Or.inr (Subtype.ext
            (by simp only [Subgroup.coe_inv, Subgroup.coe_mul]
                rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h.x_sq,
                  inv_eq_of_mul_eq_one_right h.g_sq, u_x_comm_g h])))) }
  have hcardW : Nat.card W = 4 := by
    let f : Fin 4 → W := fun k =>
      match k.val with
      | 0 => ⟨1, Or.inl rfl⟩
      | 1 => ⟨⟨g, g_mem z g⟩, Or.inr (Or.inl rfl)⟩
      | 2 => ⟨⟨x, x_mem h⟩, Or.inr (Or.inr (Or.inl rfl))⟩
      | _ => ⟨⟨g, g_mem z g⟩ * ⟨x, x_mem h⟩, Or.inr (Or.inr (Or.inr rfl))⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        fin_cases a <;> fin_cases b
        all_goals
          first
            | exact Fin.ext rfl
            | exfalso
        all_goals
          have h1 := congrArg Subtype.val hab
          have h2 := congrArg Subtype.val h1
          simp only [f, Subtype.coe_mk, Subgroup.coe_one, Subgroup.coe_mul] at h2
          first
            | exact u_g_ne_one h h2
            | exact u_g_ne_one h h2.symm
            | exact u_gx_ne_one h h2
            | exact u_gx_ne_one h h2.symm
            | exact u_g_ne_x h h2
            | exact u_g_ne_x h h2.symm
            | exact u_gx_ne_x h h2
            | exact u_gx_ne_x h h2.symm
            | exact u_gx_ne_g h h2
            | exact u_gx_ne_g h h2.symm
            | exact h.x_ne h2
            | exact h.x_ne h2.symm
      · rintro ⟨q, hq⟩
        rcases hq with rfl | rfl | rfl | rfl
        · exact ⟨⟨0, by norm_num⟩, Subtype.ext rfl⟩
        · exact ⟨⟨1, by norm_num⟩, Subtype.ext rfl⟩
        · exact ⟨⟨2, by norm_num⟩, Subtype.ext rfl⟩
        · exact ⟨⟨3, by norm_num⟩, Subtype.ext rfl⟩
    rw [← Nat.card_eq_of_bijective f hf]
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  have hindexW : W.index = 2 := by
    have hcard := W.card_mul_index
    rw [card h, hcardW] at hcard
    omega
  have hWg : ∀ q : closure ({z, g} : Set G), q ∈ W →
      q * ⟨g, g_mem z g⟩ = ⟨g, g_mem z g⟩ * q := by
    intro q hq
    rcases (show q = 1 ∨ q = ⟨g, g_mem z g⟩ ∨ q = ⟨x, x_mem h⟩ ∨
        q = ⟨g, g_mem z g⟩ * ⟨x, x_mem h⟩ from hq) with rfl | rfl | rfl | rfl
    · exact Subtype.ext (by simp)
    · exact Subtype.ext (by simp)
    · exact Subtype.ext
        (by simp only [Subgroup.coe_mul]; rw [u_x_comm_g h])
    · exact Subtype.ext
        (by simp only [Subgroup.coe_mul]
            rw [mul_assoc, u_x_comm_g h, ← mul_assoc, h.g_sq, one_mul])
  have hzW : (⟨z, z_mem z g⟩ : closure ({z, g} : Set G)) ∉ W := by
    intro hz
    have hcomm : z * g = g * z := by
      have := hWg ⟨z, z_mem z g⟩ hz
      simpa [Subtype.ext_iff] using congrArg Subtype.val this
    have hx1 : x = 1 := by
      rw [← h.x_eq, hcomm, mul_assoc g z z, h.z_sq, mul_one, h.g_sq]
    exact h.x_ne hx1
  let ε : closure ({z, g} : Set G) →* ℤˣ :=
    { toFun := fun q => if q ∈ W then (1 : ℤˣ) else -1
      map_one' := by
        show (if (1 : closure ({z, g} : Set G)) ∈ W then (1 : ℤˣ) else -1) = 1
        rw [if_pos (one_mem W)]
      map_mul' := by
        intro a b
        by_cases ha : a ∈ W <;> by_cases hb : b ∈ W <;>
          simp [ha, hb, Subgroup.mul_mem_iff_of_index_two hindexW] }
  refine ⟨ε, ?_, ?_⟩
  · show (if (⟨z, z_mem z g⟩ : closure ({z, g} : Set G)) ∈ W then (1 : ℤˣ) else -1) = -1
    rw [if_neg hzW]
  · show (if (⟨g, g_mem z g⟩ : closure ({z, g} : Set G)) ∈ W then (1 : ℤˣ) else -1) = 1
    rw [if_pos (show (⟨g, g_mem z g⟩ : closure ({z, g} : Set G)) ∈ W from
      Or.inr (Or.inl rfl))]

theorem subgroup_cases (h : D8Rel z g x) {S : Subgroup G} (hS : S ≤ closure ({z, g} : Set G))
    (hx : x ∈ S) (hz : z ∉ S) :
    S = zpowers x ∨ S = closure {g, x} ∨ S = zpowers (z * g) := by
  by_cases hzg : z * g ∈ S
  · right; right
    have hgS : g ∉ S := by
      intro hg
      apply hz
      have := mul_mem hzg hg
      rwa [mul_assoc, h.g_sq, mul_one] at this
    refine le_antisymm ?_ (Subgroup.zpowers_le.mpr hzg)
    intro q hq
    rcases (mem_closure_iff h q).mp (hS hq) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact absurd hq hz
    · exact absurd (show z ∈ S from by
        have := mul_mem hzg hq
        rwa [mul_assoc, h.g_sq, mul_one] at this) hz
    · exact mem_zpowers_iff.mpr ⟨1, by simp⟩
    · rw [show g * z = (z * g)⁻¹ from by
            rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h.z_sq,
              inv_eq_of_mul_eq_one_right h.g_sq]]
      exact inv_mem (mem_zpowers_iff.mpr ⟨1, by simp⟩)
    · exact absurd (show g ∈ S from by
        rw [← u_zgz_mul_x h]; exact mul_mem hq hx) hgS
    · exact absurd (show g ∈ S from by
        rw [← u_zg_mul_gzg h]; exact mul_mem hzg hq) hgS
    · rw [← u_A_sq_zpow h]
      exact Subgroup.zpow_mem _ (mem_zpowers_iff.mpr ⟨1, by simp⟩) 2
  · by_cases hg : g ∈ S
    · right; left
      refine le_antisymm ?_ ((Subgroup.closure_le S).mpr (by
        intro y hy
        rcases hy with rfl | rfl
        · exact hg
        · exact hx))
      intro q hq
      rcases (mem_closure_iff h q).mp (hS hq) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact absurd hq hz
      · exact subset_closure (by simp)
      · exact absurd hq hzg
      · exact absurd (show z ∈ S from by
          rw [← u_g_mul_gz h]; exact mul_mem hg hq) hz
      · rw [← u_g_mul_x h]
        exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
      · exact absurd (show z * g ∈ S from by
          rw [← u_g_mul_gzg h]; exact mul_mem hg hq) hzg
      · exact subset_closure (by simp)
    · left
      refine le_antisymm ?_ (Subgroup.zpowers_le.mpr hx)
      intro q hq
      rcases (mem_closure_iff h q).mp (hS hq) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact absurd hq hz
      · exact absurd hq hg
      · exact absurd hq hzg
      · exact absurd (show z * g ∈ S from by
          rw [← u_inv_gz h]; exact inv_mem hq) hzg
      · exact absurd (show g ∈ S from by
          rw [← u_zgz_mul_x h]; exact mul_mem hq hx) hg
      · exact absurd (show z ∈ S from by
          rw [← u_gzg_mul_x h]; exact mul_mem hq hx) hz
      · exact mem_zpowers_iff.mpr ⟨1, by simp⟩

end D8Rel

end CFSG.OddStandard.AltStdSec.SwapPartner
