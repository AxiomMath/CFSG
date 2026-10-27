module

public import Certificates.Data.Kernel.PermCent.F7Cent
public import CFSG.Certificates.Kernel.PermCent.F7CSound

public section

namespace CFSG.Certificates.Kernel.PkCV

open Equiv Equiv.Perm CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2.Model
  CFSG.GH74.GLS.C3.Prop121.Card7 CFSG.GH74.GLS.C3.Prop121.Card7.FF

theorem forceQL_eq {m k : Nat} {β : Sort _} :
    ∀ (l : List (CV m × CV k)) (c : List (CV m × CV k) → β), forceQL l c = c l
  | [], _ => rfl
  | a :: l, c => by
    rw [forceQL, forceC_eq, forceC_eq, forceQL_eq l]

theorem flatMap_filter_of {α β : Type*} (L : List α) (g : α → List β) (p : β → Bool) (t : α → Bool)
    (h : ∀ x ∈ L, (g x).filter p = if t x then g x else []) :
    (L.flatMap g).filter p = (L.filter t).flatMap g := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.flatMap_cons, List.filter_append, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem a hx), List.filter_cons]
    cases t a <;> simp

@[expose] noncomputable def evF7 (a : CV 7 × CV 4) : Amb 7 := (ev a.1, ev a.2)

theorem decide_comm_pair (ρ : Perm (Fin 7)) (a : CV 7) (b : CV 4) :
    decide ((ev a, ev b) * (ρ, (1 : Perm (Fin 4))) = (ρ, 1) * (ev a, ev b)) =
      eq22C a (cOf ρ) (cOf ρ) a := by
  rw [← comm_fast, ← decide_comm_ev]
  simp only [Prod.mk_mul_mk, mul_one, one_mul, Prod.mk.injEq, and_true]

theorem decide_comm_val (u c : F7) :
    decide (c * u = u * c) = decide ((c : Amb 7) * (u : Amb 7) = (u : Amb 7) * (c : Amb 7)) := by
  simp only [Subtype.ext_iff, Subgroup.coe_mul]

theorem map_filter_comm (u : F7) (ρ : Perm (Fin 7)) (hu : (u : Amb 7) = (ρ, 1)) :
    (F7L.filter fun c => decide (c * u = u * c)).map Subtype.val = (CF7 (cOf ρ)).map evF7 := by
  have h1 : (F7L.filter fun c => decide (c * u = u * c)) =
      F7L.filter ((fun a : Amb 7 => decide (a * (ρ, 1) = (ρ, 1) * a)) ∘ Subtype.val) := by
    apply List.filter_congr
    intro c _
    rw [decide_comm_val, hu]
    rfl
  rw [h1, ← List.filter_map, F7L_eq, List.filter_map]
  have h2 : F7C.filter ((fun a : Amb 7 => decide (a * (ρ, 1) = (ρ, 1) * a)) ∘
      fun a => (ev a.1, ev a.2)) = CF7 (cOf ρ) := by
    unfold F7C CF7
    rw [forcePL_eq, forcePL_eq, forcePL_eq, forcePL_eq]
    apply flatMap_filter_of
    intro x _
    rw [List.filter_map]
    have hc : ∀ y : CV 4 × Bool,
        (((fun a : Amb 7 => decide (a * (ρ, 1) = (ρ, 1) * a)) ∘ fun a => (ev a.1, ev a.2)) ∘
          fun y => (x.1, y.1)) y = eq22C x.1 (cOf ρ) (cOf ρ) x.1 := fun y =>
      decide_comm_pair ρ x.1 y.1
    rw [List.filter_congr (fun y _ => hc y)]
    cases eq22C x.1 (cOf ρ) (cOf ρ) x.1 <;> simp
  rw [h2]
  rfl

theorem ccardB_self (u : F7) (ρ : Perm (Fin 7)) (hu : (u : Amb 7) = (ρ, 1)) :
    ccardB u u = (CF7 (cOf ρ)).length := by
  rw [← List.length_map (f := evF7), ← map_filter_comm u ρ hu, List.length_map, ccardB,
    List.countP_eq_length_filter]
  congr 2
  funext c
  simp only [and_self]

end CFSG.Certificates.Kernel.PkCV

end
