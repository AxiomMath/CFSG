module

public import Certificates.Data.Kernel.PermCent.Moore7C
public import CFSG.Certificates.Kernel.PermCent.AllPermsCSound

public section

namespace CFSG.Certificates.Kernel.PkCV

open Equiv Equiv.Perm CFSG.GH74.GLS.C3.Prop121

theorem m7_ite_true (c : Prop) [Decidable c] (x : Bool) :
    (if c then x else true) = (!decide c || x) := by
  by_cases h : c <;> simp [h]

theorem m7_beq (a b : CV 8) : Nat.beq a.1 b.1 = decide (a = b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff, Subtype.ext_iff]

theorem m7_sign (σ : Perm (Fin 8)) : sign σ = 1 ↔ ¬ sign σ = -1 := by
  rcases Int.units_eq_one_or (sign σ) with h | h <;> rw [h] <;> decide

theorem m7AllB_eq (A O E : List (CV 8)) :
    okAll7 (A.map ev) (O.map ev) (E.map ev) = m7AllB A O E := by
  unfold okAll7 okB7 okC7 m7AllB m7BB m7CB
  simp only [forceCL_eq, List.all_map, List.filter_map, Function.comp_def, ev_mul', ev_pow',
    one_eq_ev, ev_eq_iff, m7_ite_true, ne_eq, decide_not, Bool.not_not, eq22C_eq, powOneC_eq,
    m7_beq, Bool.or_assoc]

theorem m7E_eq (c : CV 8) :
    (allPerms 8).filter (fun s => decide (s * s = 1 ∧ sign s = 1 ∧ s * ev c * s⁻¹ = (ev c)⁻¹)) =
      (m7E (m7Inv (allPermsP 8 inferInstance)) c c⁻¹).map ev := by
  rw [allPerms_eq 8 inferInstance, m7E, m7Inv, List.filter_filter, List.filter_map, List.map_map]
  refine congrArg₂ List.map rfl (List.filter_congr fun x hx => ?_)
  rw [Function.comp_apply, par_of_mem_allPermsP hx, powOneC_eq, pow_two, ← conj_fast]
  simp only [ev_mul', ev_inv', one_eq_ev, ev_eq_iff, m7_sign]
  by_cases h1 : x.1 * x.1 = 1 <;> by_cases h2 : sign (ev x.1) = -1 <;>
    by_cases h3 : x.1 * c * x.1⁻¹ = c⁻¹ <;> simp [h1, h2, h3]

theorem m7O_eq (c : CV 8) :
    (allPerms 8).filter (fun s => decide (s * s = 1 ∧ sign s = -1 ∧ s * ev c * s⁻¹ = (ev c)⁻¹)) =
      (m7O (m7Inv (allPermsP 8 inferInstance)) c c⁻¹).map ev := by
  rw [allPerms_eq 8 inferInstance, m7O, m7Inv, List.filter_filter, List.filter_map, List.map_map]
  refine congrArg₂ List.map rfl (List.filter_congr fun x hx => ?_)
  rw [Function.comp_apply, par_of_mem_allPermsP hx, powOneC_eq, pow_two, ← conj_fast]
  simp only [ev_mul', ev_inv', one_eq_ev, ev_eq_iff]
  by_cases h1 : x.1 * x.1 = 1 <;> by_cases h2 : sign (ev x.1) = -1 <;>
    by_cases h3 : x.1 * c * x.1⁻¹ = c⁻¹ <;> simp [h1, h2, h3]

theorem m7A_eq (c : CV 8) :
    (allPerms 8).filter (fun s => decide (s * s = 1 ∧ sign s = 1 ∧ s ≠ 1 ∧ (ev c * s) ^ 3 = 1)) =
      (m7A (m7Inv (allPermsP 8 inferInstance)) c).map ev := by
  rw [allPerms_eq 8 inferInstance, m7A, m7Inv, List.filter_filter, List.filter_map, List.map_map]
  refine congrArg₂ List.map rfl (List.filter_congr fun x hx => ?_)
  rw [Function.comp_apply, par_of_mem_allPermsP hx, powOneC_eq, powOneC_eq, powOneC_eq, pow_two,
    pow_one]
  simp only [ev_mul', ev_pow', one_eq_ev, ev_eq_iff, ne_eq, m7_sign]
  by_cases h1 : x.1 * x.1 = 1 <;> by_cases h2 : sign (ev x.1) = -1 <;> by_cases h3 : x.1 = 1 <;>
    by_cases h4 : (c * x.1) ^ 3 = 1 <;> simp [h1, h2, h3, h4]

theorem evenL7_eq :
    evenL7 = (m7E (m7Inv (allPermsP 8 inferInstance)) (cOf cEnd7) (cOf cEnd7)⁻¹).map ev := by
  rw [evenL7]
  conv_lhs => rw [eq_ev_cOf cEnd7]
  exact m7E_eq _

theorem oddL7_eq :
    oddL7 = (m7O (m7Inv (allPermsP 8 inferInstance)) (cOf cEnd7) (cOf cEnd7)⁻¹).map ev := by
  rw [oddL7]
  conv_lhs => rw [eq_ev_cOf cEnd7]
  exact m7O_eq _

theorem a4L7_eq : a4L7 = (m7A (m7Inv (allPermsP 8 inferInstance)) (cOf cEnd7)).map ev := by
  rw [a4L7]
  conv_lhs => rw [eq_ev_cOf cEnd7]
  exact m7A_eq _

theorem okAll7_eq : okAll7 a4L7 oddL7 evenL7 = m7F := by
  rw [a4L7_eq, oddL7_eq, evenL7_eq, m7AllB_eq, m7F, forceC_eq, forceC_eq, forcePL_eq, forceCL_eq,
    forceCL_eq, forceCL_eq]

end CFSG.Certificates.Kernel.PkCV

end
