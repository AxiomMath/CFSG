module

public import Certificates.Data.Kernel.PermCent.AllPermsC
public import CFSG.Certificates.Kernel.PermCent.ForceCVSound
public import CFSG.GH74.GLS.C3.Prop121.MooreFinite7Inputs
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.Certificates.Kernel.PkCV

open Equiv Equiv.Perm CFSG.GH74.GLS.C3.Prop121 CFSG.KC.Enum

variable {n : Nat}

theorem forceB_eq {β : Sort _} (b : Bool) (k : Bool → β) : forceB b k = k b := by
  cases b <;> rfl

theorem forcePL_eq {β : Sort _} :
    ∀ (l : List (CV n × Bool)) (k : List (CV n × Bool) → β), forcePL l k = k l
  | [], _ => rfl
  | a :: l, k => by
    rw [forcePL, forceC_eq, forceB_eq, forcePL_eq l]

theorem ev_ofFnC [hs : Small n] (f : Nat → Nat) (σ : Equiv.Perm (Fin n))
    (h : ∀ i (hi : i < n), f i = σ ⟨i, hi⟩) : ev (ofFnC f σ h) = σ := by
  ext i
  rw [ev_apply]
  have hf : ∀ x < n, f x < 2 ^ wC n := fun x hx => by
    rw [h x hx]
    exact (σ _).2.trans (by have := lt_wC n; omega)
  change pg (wC n) (CFSG.KS.mask (wC n)) (pmk n (wC n) f) i = _
  rw [pg_pmk hs.lt hf i.2, h i i.2]

theorem ev_liftC {m : Nat} [Small m] [Small (m + 1)] (p : Fin (m + 1)) (e : CV m) :
    ev (liftC p e) = decomposeFin.symm (p, ev e) :=
  ev_ofFnC _ _ _

theorem par_decomposeFin_symm {m : Nat} (p : Fin (m + 1)) (e : Perm (Fin m)) :
    decide (sign (decomposeFin.symm (p, e)) = -1) = xor (p.1 != 0) (decide (sign e = -1)) := by
  rw [decomposeFin.symm_sign]
  have hp : (p.1 != 0) = !decide (p = 0) := by
    by_cases hp : p = 0
    · simp [hp]
    · have : p.1 ≠ 0 := fun h => hp (Fin.ext h)
      simp [hp, this]
  rw [hp]
  rcases Int.units_eq_one_or (sign e) with h | h <;> by_cases hp0 : p = 0 <;> simp [h, hp0]

theorem allPermsP_spec : ∀ (m : Nat) (hs : Small m),
    (allPermsP m hs).map (fun x => (ev x.1, x.2)) =
      (allPerms m).map fun r => (r, decide (sign r = -1))
  | 0, hs => by
    simp [allPermsP, allPerms, ev_one]
  | m + 1, hs => by
    have : Small m := small_pred hs
    have ih := allPermsP_spec m this
    rw [allPermsP, forcePL_eq, allPerms, List.map_flatMap, List.map_flatMap]
    congr 1
    funext p
    rw [List.map_map, List.map_map]
    have h1 : ((fun x : CV (m + 1) × Bool => (ev x.1, x.2)) ∘
        fun x : CV m × Bool => (liftC p x.1, xor (p.1 != 0) x.2)) =
        (fun y : Perm (Fin m) × Bool => (decomposeFin.symm (p, y.1), xor (p.1 != 0) y.2)) ∘
          (fun x : CV m × Bool => (ev x.1, x.2)) := by
      funext x
      simp only [Function.comp_apply, ev_liftC]
    rw [h1, ← List.map_map, ih, List.map_map]
    congr 1
    funext r
    simp only [Function.comp_apply, par_decomposeFin_symm]

theorem allPerms_eq (m : Nat) (hs : Small m) :
    allPerms m = (allPermsP m hs).map fun x => ev x.1 := by
  have h := congrArg (List.map Prod.fst) (allPermsP_spec m hs)
  simp only [List.map_map, Function.comp_def] at h
  rw [h]
  simp

theorem par_of_mem_allPermsP {m : Nat} {hs : Small m} {x : CV m × Bool} (hx : x ∈ allPermsP m hs) :
    x.2 = decide (sign (ev x.1) = -1) := by
  have h : (ev x.1, x.2) ∈ (allPerms m).map fun r => (r, decide (sign r = -1)) := by
    rw [← allPermsP_spec m hs]
    exact List.mem_map_of_mem hx
  obtain ⟨r, -, hr⟩ := List.mem_map.1 h
  rw [Prod.mk.injEq] at hr
  rw [← hr.2, hr.1]

end CFSG.Certificates.Kernel.PkCV

end
