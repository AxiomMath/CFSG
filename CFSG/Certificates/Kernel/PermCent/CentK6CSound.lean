module

public import Certificates.Data.Kernel.PermCent.CentK6C
public import CFSG.Certificates.Kernel.PermCent.Ok122CSound
public import CFSG.GH74.GLS.C3.Prop121.CentKFinInputs

public section

namespace CFSG.Certificates.Kernel.PkCV

open Equiv Equiv.Perm CFSG.GH74.GLS.C3.Prop121

variable {n : Nat}

theorem forceOL_eq {β : Sort _} :
    ∀ (l : List (CV n × List (CV n))) (k : List (CV n × List (CV n)) → β), forceOL l k = k l
  | [], _ => rfl
  | a :: l, k => by
    rw [forceOL, forceC_eq, forceCL_eq, forceOL_eq l]

theorem sign_dec {m : Nat} (σ : Perm (Fin m)) : decide (sign σ = 1) = !decide (sign σ = -1) := by
  rcases Int.units_eq_one_or (sign σ) with h | h <;> rw [h] <;> decide

theorem evenP_eq (m : Nat) (hs : Small m) :
    (allPerms m).filter (fun s => decide (sign s = 1)) = (evenP (allPermsP m hs)).map ev := by
  rw [allPerms_eq m hs, evenP, List.filter_map, List.map_map]
  refine congrArg₂ List.map rfl (List.filter_congr fun x hx => ?_)
  rw [Function.comp_apply, par_of_mem_allPermsP hx, sign_dec]

theorem even6_eq : even6 = (evenP (allPermsP 6 inferInstance)).map ev := by
  unfold even6
  exact evenP_eq 6 inferInstance

theorem inv6_eq : inv6 = (inv6P (allPermsP 6 inferInstance)).map ev := by
  unfold inv6 inv6P
  rw [allPerms_eq 6 inferInstance, List.filter_map, List.map_map]
  refine congrArg₂ List.map rfl (List.filter_congr fun x hx => ?_)
  rw [Function.comp_apply, par_of_mem_allPermsP hx, powOneC_eq, powOneC_eq, pow_one, pow_two]
  simp only [ev_mul', one_eq_ev, ne_eq, ev_eq_iff, sign_eq_one_iff]
  by_cases h1 : x.1 * x.1 = 1 <;> by_cases h2 : x.1 = 1 <;>
    by_cases h3 : sign (ev x.1) = -1 <;> simp [h1, h2, h3]

theorem ord3six_eq : ord3six = (ord6P (allPermsP 6 inferInstance)).map ev := by
  unfold ord3six ord6P
  rw [allPerms_eq 6 inferInstance, List.filter_map, List.map_map]
  refine congrArg₂ List.map rfl (List.filter_congr fun x _ => ?_)
  rw [Function.comp_apply, powOneC_eq, powOneC_eq, pow_one, pow_three']
  simp only [ev_mul', one_eq_ev, ev_eq_iff, Bool.decide_and, decide_not]

theorem okC6_eq_B (I O E : List (CV 6)) (hI : inv6 = I.map ev) (hO : ord3six = O.map ev)
    (hE : even6 = E.map ev) : okC6 = c6B I (O.map fun τ => (τ, E.filter fun b => cmC b τ)) := by
  unfold okC6 okP6 okT6 okB6 goodW c6B gWC
  rw [hI, hO, hE]
  simp only [forceC_eq, List.all_map, List.all_filter, Function.comp_def, ite_true_eq, ev_mul',
    ev_inv', one_eq_ev, ev_eq_iff, ne_eq, cmC_eq, ← conj_fast, powOneC_eq, pow_one, beq_val,
    Bool.decide_and, Bool.decide_or, decide_not, Bool.not_and, Bool.not_not, Bool.or_assoc,
    Bool.and_assoc]

theorem okC6_eq : okC6 = c6F := by
  rw [c6F, forcePL_eq, forceCL_eq, forceCL_eq, forceCL_eq, forceOL_eq]
  exact okC6_eq_B _ _ _ inv6_eq ord3six_eq even6_eq

theorem five_eq : ((allPerms 5).all fun τ =>
      !(decide (τ * τ * τ = 1 ∧ τ ≠ 1)) ||
        (allPerms 5).all fun b =>
          !(decide (sign b = 1 ∧ b * τ = τ * b)) ||
            decide (b = 1 ∨ b = τ ∨ b = τ⁻¹)) = f5F := by
  have hin : ∀ τ : Perm (Fin 5), ((allPerms 5).all fun b =>
      !(decide (sign b = 1 ∧ b * τ = τ * b)) || decide (b = 1 ∨ b = τ ∨ b = τ⁻¹)) =
      ((evenP (allPermsP 5 inferInstance)).map ev).all fun b =>
        !decide (b * τ = τ * b) || decide (b = 1 ∨ b = τ ∨ b = τ⁻¹) := by
    intro τ
    rw [← evenP_eq 5 inferInstance]
    simp only [List.all_filter, Bool.decide_and, Bool.not_and, Bool.or_assoc]
  simp only [hin]
  rw [f5F, forcePL_eq, forceCL_eq, allPerms_eq 5 inferInstance]
  simp only [forceC_eq, List.all_map, Function.comp_def, ev_mul', ev_inv', one_eq_ev, ev_eq_iff,
    ne_eq, cmC_eq, powOneC_eq, pow_one, pow_three', beq_val, Bool.decide_and, Bool.decide_or,
    decide_not, Bool.not_and, Bool.not_not, Bool.or_assoc, Bool.and_assoc]

end CFSG.Certificates.Kernel.PkCV

end
