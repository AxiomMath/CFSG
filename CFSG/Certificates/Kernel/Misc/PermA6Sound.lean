module

public import Certificates.Data.Kernel.Misc.PermA6
public import CFSG.Certificates.Kernel.Misc.PermClosSound
public import CFSG.RankThree.Native.ONTripleA6Inputs
import CFSG.Certificates.Kernel.LocalQTPermSound
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.Misc.A6

open Equiv CFSG.KC.LQT CFSG.KC.Misc.Clos CFSG.RankThree.Native.ONTriple

theorem pcode_even {n : ℕ} (hn : n ≤ 32) (σ : Perm (Fin n))
    (h : CFSG.KC.LQT.P.even n (pcode σ) = true) : Perm.sign σ = 1 :=
  (P.even_code hn σ).1 h

theorem h6 : (6 : ℕ) ≤ 32 := by norm_num

theorem d1K_sound (κ : Perm (Fin 6)) (sv : ℕ → ℕ → Perm (Fin 6)) {Y : ℕ} {V : ℕ → ℕ}
    (hY : pcode κ = Y) (hV : ∀ m < 3, ∀ i < 3, pcode (sv m i) = V (3 * m + i))
    (h : d1K Y V = true) :
    ∀ t : Perm (Fin 6), Perm.sign t = 1 → t ^ 4 = 1 → t ≠ 1 →
      (∃ m < 3, ∃ i < 3, t = sv m i) ∨ (cand1 κ t).any (fun u => u ^ 4 != 1) := by
  intro t h1 h2 h3
  subst hY
  have h' : d1K (P.code κ) V = true := h
  have ht := (P.allP_iff (n := 6) _).1 h' t
  simp only [p4, cjK, P.impB_iff, P.notB_iff, P.orB_iff, P.anyN_iff, P.letB_eq, P.even_code h6,
    P.code_one, P.code_pow h6, P.code_inv h6, P.code_mul h6, P.beq_iff, P.code_eq_iff h6,
    Nat.add_eq, Nat.mul_eq] at ht
  rcases ht h1 h2 h3 with ⟨m, hm, i, hi, e⟩ | hB
  · left
    refine ⟨m, hm, i, hi, ?_⟩
    rw [← hV m hm i hi] at e
    exact (P.code_eq_iff h6).1 e
  · right
    simp only [cand1, cj, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
      bne_iff_ne, ne_eq]
    exact hB

theorem d2K_sound (κ v₀ v₁ v₂ : Perm (Fin 6)) {Y A B C : ℕ} (hY : pcode κ = Y)
    (h₀ : pcode v₀ = A) (h₁ : pcode v₁ = B) (h₂ : pcode v₂ = C) (h : d2K Y A B C = true) :
    ∀ s : Perm (Fin 6), Perm.sign s = 1 → s ^ 4 = 1 → s ≠ 1 → s ≠ v₀ → s ≠ v₁ → s ≠ v₂ →
      (cand2 κ s [1, v₀, v₁, v₂]).any (fun u => u ^ 4 != 1) := by
  intro s h1 h2 h3 h4 h5 h6'
  subst hY h₀ h₁ h₂
  have h' : d2K (P.code κ) (P.code v₀) (P.code v₁) (P.code v₂) = true := h
  have ht := (P.allP_iff (n := 6) _).1 h' s
  simp only [p4, cjK, cand2K, P.impB_iff, P.notB_iff, P.orB_iff, P.anyL_iff, P.letB_eq,
    P.even_code h6, P.code_one, P.code_pow h6, P.code_inv h6, P.code_mul h6, P.beq_iff,
    P.code_eq_iff h6, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left] at ht
  have hB := ht h1 h2 h3 (by tauto)
  simp only [cand2, cj, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, bne_iff_ne, ne_eq]
  exact hB

end CFSG.KC.Misc.A6

end
