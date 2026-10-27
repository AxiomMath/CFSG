module

public import CFSG.Sporadic.SchreierLemmas.MoorePresentation
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm CFSG.Sporadic.SchreierLemmas

@[expose] def cs (n k : ℕ) : Perm (Fin (n + 1)) :=
  if h : k < n then swap ⟨k, by omega⟩ ⟨k + 1, by omega⟩ else 1

theorem cs_of_lt {n k : ℕ} (h : k < n) :
    cs n k = swap ⟨k, by omega⟩ ⟨k + 1, by omega⟩ := by
  simp [cs, h]

theorem cs_of_ge {n k : ℕ} (h : n ≤ k) : cs n k = 1 := by
  simp [cs, Nat.not_lt.2 h]

theorem cs_mul_self (n k : ℕ) : cs n k * cs n k = 1 := by
  by_cases h : k < n
  · rw [cs_of_lt h]; exact swap_mul_self _ _
  · rw [cs_of_ge (Nat.not_lt.1 h)]; exact mul_one 1

theorem cs_inv (n k : ℕ) : (cs n k)⁻¹ = cs n k :=
  inv_eq_of_mul_eq_one_right (cs_mul_self n k)

theorem cs_comm (n : ℕ) {k l : ℕ} (h : k + 2 ≤ l) : cs n k * cs n l = cs n l * cs n k := by
  by_cases hl : l < n
  · have hk : k < n := by omega
    rw [cs_of_lt hl, cs_of_lt hk]
    refine (swap_mul_swap_comm ?_ ?_ ?_ ?_).symm <;> simp [Fin.ext_iff] <;> omega
  · rw [cs_of_ge (Nat.not_lt.1 hl)]; simp

theorem cs_braid (n : ℕ) {k : ℕ} (h : k + 1 < n) : (cs n k * cs n (k + 1)) ^ 3 = 1 := by
  have hk : k < n := by omega
  rw [cs_of_lt hk, cs_of_lt h]
  exact swap_mul_swap_pow_three' (by simp only [ne_eq, Fin.mk.injEq]; omega)
    (by simp only [ne_eq, Fin.mk.injEq]; omega) (by simp only [ne_eq, Fin.mk.injEq]; omega)

theorem sign_cs {n k : ℕ} (h : k < n) : sign (cs n k) = -1 := by
  rw [cs_of_lt h]; exact sign_swap (by simp [Fin.ext_iff])

theorem cs_apply_zero {n k : ℕ} (hk : 1 ≤ k) : cs n k 0 = 0 := by
  by_cases h : k < n
  · rw [cs_of_lt h]
    exact swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff])
  · rw [cs_of_ge (Nat.not_lt.1 h)]; rfl

theorem cs_injective {n k l : ℕ} (hk : k < n) (hl : l < n) (h : cs n k = cs n l) : k = l := by
  rw [cs_of_lt hk, cs_of_lt hl] at h
  by_contra hne
  have h1 := congrArg (fun p => p ⟨k, by omega⟩) h
  simp only [swap_apply_def] at h1
  split_ifs at h1 <;> simp_all [Fin.ext_iff]
  all_goals omega

@[expose] def cEnd (n : ℕ) : Perm (Fin (n + 1)) := cs n (n - 2) * cs n (n - 1)

theorem isThreeCycle_cEnd {n : ℕ} (hn : 3 ≤ n) : (cEnd n).IsThreeCycle := by
  unfold cEnd
  rw [cs_of_lt (by omega : n - 2 < n), cs_of_lt (by omega : n - 1 < n)]
  have h1 : n - 2 + 1 = n - 1 := by omega
  have h2 : n - 1 + 1 = n := by omega
  have e : (⟨n - 2 + 1, by omega⟩ : Fin (n + 1)) = ⟨n - 1, by omega⟩ := Fin.ext h1
  have e2 : (⟨n - 1 + 1, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := Fin.ext h2
  rw [e, e2]
  have := isThreeCycle_swap_mul_swap_same (α := Fin (n + 1))
    (a := (⟨n - 1, by omega⟩ : Fin (n + 1))) (b := ⟨n - 2, by omega⟩) (c := ⟨n, by omega⟩)
    (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)
  rwa [swap_comm] at this

theorem cEnd_apply_zero {n : ℕ} (hn : 3 ≤ n) : cEnd n 0 = 0 := by
  unfold cEnd
  simp only [Perm.mul_apply]
  rw [cs_apply_zero (by omega), cs_apply_zero (by omega)]

structure PhiData {G : Type} [Group G] {n : ℕ} (K L : Subgroup G) (u : G)
    (φ : Perm (Fin (n + 1)) →* G) : Prop where
  inj : Function.Injective φ
  mem : ∀ p, φ p ∈ L ⊔ zpowers u
  surj : ∀ y ∈ L ⊔ zpowers u, ∃ p, φ p = y
  alt : ∀ p, φ p ∈ L ↔ sign p = 1
  stab : ∀ p, φ p ∈ K ⊔ zpowers u ↔ p 0 = 0

end CFSG.GH74.GLS.C3.Prop121
