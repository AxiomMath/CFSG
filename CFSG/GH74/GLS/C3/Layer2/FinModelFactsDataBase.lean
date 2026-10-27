
module

public import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public import CFSG.GH74.GLS.C3.Layer2.FinModelFactsDataInputs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelFactsDataInputs
public import CFSG.GH74.GLS.C3.Layer2.FinModelFactsMath

@[expose] public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm CFSG.GH74.GLS.C3.Layer2

namespace Facts

theorem flatPerm_eq {m : ℕ} (p : Perm (Fin m)) : flatPerm p = p := by
  ext i
  simp [flatPerm, flatPermAux]

theorem evalWord_eq {m r : ℕ} (y : Fin r → Perm (Fin m)) (w : List (Fin r)) :
    evalWord y w = (w.map y).prod := flatPerm_eq _

theorem a0f_eq (n : ℕ) [NeZero n] : a0f n = a0perm n := flatPerm_eq _

theorem y0p_eq (n : ℕ) [NeZero n] : y0p n = emb n (x0 n) := flatPerm_eq _

theorem mem_Rl_iff (n : ℕ) [NeZero n] (p : Perm (Fin (n + 4))) :
    p ∈ Rl n ↔ ∃ t ∈ Tl n, emb n t = p := by
  simp [Rl, flatPerm_eq]

theorem mem_Sl_iff (n : ℕ) [NeZero n] (hsq : a0perm n * a0perm n = 1)
    (p : Perm (Fin (n + 4))) : p ∈ Sl n ↔ p ∈ Rl n ∨ p * a0perm n ∈ Rl n := by
  simp only [Sl, List.mem_append, List.mem_map, flatPerm_eq, a0f_eq]
  refine or_congr_right ⟨?_, ?_⟩
  · rintro ⟨q, hq, rfl⟩
    rwa [mul_assoc, hsq, mul_one]
  · intro h
    exact ⟨p * a0perm n, h, by rw [mul_assoc, hsq, mul_one]⟩

theorem mem_Cl_iff (n : ℕ) [NeZero n] (p : Perm (Fin (n + 4))) :
    p ∈ Cl n ↔ p ∈ Sl n ∧ a0perm n * p = p * a0perm n := by
  simp [Cl, a0f_eq]

theorem Cl_nodup (n : ℕ) [NeZero n] (h : (Sl n).Nodup) : (Cl n).Nodup := h.filter _

end Facts

end CFSG.GH74.GLS.C3.Layer2.Model
