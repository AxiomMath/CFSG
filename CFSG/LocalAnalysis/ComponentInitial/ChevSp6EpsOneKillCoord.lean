module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneKillFacts
public import Batteries.Data.Nat.Bitwise.Lemmas
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

open Subgroup

structure KillData {G : Type*} [Group G] (u : Bool) (Jh E : Subgroup G) (cV cE : G → ℕ)
    (z l₁ l₂ : G) : Prop where
  E_le : E ≤ Jh
  cV_lt : ∀ x ∈ Jh, cV x < 64
  cV_mul : ∀ x ∈ Jh, ∀ y ∈ Jh, cV (x * y) = cV x ^^^ cV y
  cV_eq_zero : ∀ x ∈ Jh, cV x = 0 ↔ x ∈ E
  cV_surj : ∀ v, v < 64 → ∃ x ∈ Jh, cV x = v
  cE_lt : ∀ x ∈ E, cE x < 512
  cE_mul : ∀ x ∈ E, ∀ y ∈ E, cE (x * y) = cE x ^^^ cE y
  cE_inj : ∀ x ∈ E, cE x = 0 → x = 1
  cE_surj : ∀ e, e < 512 → ∃ x ∈ E, cE x = e
  sq : ∀ x ∈ Jh, x * x ∈ E ∧ cE (x * x) = qOf u (cV x)
  central : ∀ e ∈ E, ∀ x ∈ Jh, e * x = x * e
  z_norm : z ∈ normalizer (Jh : Set G)
  z_sq : z * z = 1
  z_act : ∀ x ∈ Jh, cV (z * x * z⁻¹) = evalV z0T (cV x)
  l₁_norm : l₁ ∈ normalizer (Jh : Set G)
  l₁_act : ∀ x ∈ Jh, cV (l₁ * x * l₁⁻¹) = evalV lam1T (cV x)
  l₂_norm : l₂ ∈ normalizer (Jh : Set G)
  l₂_act : ∀ x ∈ Jh, cV (l₂ * x * l₂⁻¹) = evalV lam2T (cV x)
  ker : ∀ P : Subgroup G, IsPGroup 2 P →
    (∀ x ∈ P, x ∈ normalizer (Jh : Set G) ∧ ∀ j ∈ Jh, cV (x * j * x⁻¹) = cV j) →
    Nat.card P ≤ 2 ^ 15
  index2 : ∀ K : Subgroup G, K.index = 2 → z ∈ K
  cent : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({z} : Set G) → Nat.card P ≤ 2 ^ 10

theorem xor_self_eq {a b : ℕ} (hab : a = a ^^^ b) : b = 0 := by
  have := congrArg (a ^^^ ·) hab
  simp at this
  omega

theorem Jh_le_X {G : Type*} [Group G] {Jh : Subgroup G} : Jh ≤ normalizer (Jh : Set G) :=
  le_normalizer

theorem conj_mem_Jh {G : Type*} [Group G] {Jh : Subgroup G} {g x : G}
    (hg : g ∈ normalizer (Jh : Set G)) (hx : x ∈ Jh) :
    g * x * g⁻¹ ∈ Jh :=
  (mem_normalizer_iff.1 hg x).1 hx

theorem conj_inv_mem_Jh {G : Type*} [Group G] {Jh : Subgroup G} {g x : G}
    (hg : g ∈ normalizer (Jh : Set G)) (hx : x ∈ Jh) :
    g⁻¹ * x * g ∈ Jh := by
  have := conj_mem_Jh (inv_mem hg) hx
  rwa [inv_inv] at this

namespace KillData

variable {G : Type*} [Group G] {u : Bool} {Jh E : Subgroup G} {cV cE : G → ℕ} {z l₁ l₂ : G}
  (h : KillData u Jh E cV cE z l₁ l₂)
include h

theorem cV_one : cV 1 = 0 := by
  have := h.cV_mul 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at this
  exact xor_self_eq this

theorem cE_one : cE 1 = 0 := by
  have := h.cE_mul 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at this
  exact xor_self_eq this

theorem cV_inv {x : G} (hx : x ∈ Jh) : cV x⁻¹ = cV x := by
  have := h.cV_mul x hx x⁻¹ (inv_mem hx)
  rw [mul_inv_cancel, h.cV_one] at this
  have h2 := congrArg (cV x ^^^ ·) this
  simp at h2
  exact h2.symm

theorem cE_inv {x : G} (hx : x ∈ E) : cE x⁻¹ = cE x := by
  have := h.cE_mul x hx x⁻¹ (inv_mem hx)
  rw [mul_inv_cancel, h.cE_one] at this
  have h2 := congrArg (cE x ^^^ ·) this
  simp at h2
  exact h2.symm

theorem E_sq {e : G} (he : e ∈ E) : e * e = 1 :=
  h.cE_inj _ (mul_mem he he) (by rw [h.cE_mul e he e he, Nat.xor_self])

theorem E_inv_eq {e : G} (he : e ∈ E) : e⁻¹ = e :=
  inv_eq_of_mul_eq_one_right (h.E_sq he)

theorem cE_injOn {x y : G} (hx : x ∈ E) (hy : y ∈ E) (hxy : cE x = cE y) : x = y := by
  have h1 := h.cE_inj (x⁻¹ * y) (mul_mem (inv_mem hx) hy) (by
    rw [h.cE_mul _ (inv_mem hx) _ hy, h.cE_inv hx, hxy, Nat.xor_self])
  rw [← mul_left_cancel_iff (a := x⁻¹), h1, inv_mul_cancel]

theorem mem_E_of_cV_eq {x y : G} (hx : x ∈ Jh) (hy : y ∈ Jh) (hxy : cV x = cV y) :
    x⁻¹ * y ∈ E :=
  (h.cV_eq_zero _ (mul_mem (inv_mem hx) hy)).1 (by
    rw [h.cV_mul _ (inv_mem hx) _ hy, h.cV_inv hx, hxy, Nat.xor_self])

theorem comm_mem_E {x y : G} (hx : x ∈ Jh) (hy : y ∈ Jh) : x⁻¹ * y⁻¹ * x * y ∈ E := by
  refine (h.cV_eq_zero _ (mul_mem (mul_mem (mul_mem (inv_mem hx) (inv_mem hy)) hx) hy)).1 ?_
  rw [h.cV_mul _ (mul_mem (mul_mem (inv_mem hx) (inv_mem hy)) hx) _ hy,
    h.cV_mul _ (mul_mem (inv_mem hx) (inv_mem hy)) _ hx, h.cV_mul _ (inv_mem hx) _ (inv_mem hy),
    h.cV_inv hx, h.cV_inv hy]
  simp [Nat.xor_comm]

theorem cE_comm {x y : G} (hx : x ∈ Jh) (hy : y ∈ Jh) :
    cE (x⁻¹ * y⁻¹ * x * y) = betaOf u (cV x) (cV y) := by
  set c := x⁻¹ * y⁻¹ * x * y with hc
  have hcE : c ∈ E := h.comm_mem_E hx hy
  have hcJ : c ∈ Jh := h.E_le hcE
  have hci : c⁻¹ = c := h.E_inv_eq hcE
  have hyx : y * x = x * y * c := by
    have : x * y = y * x * c := by rw [hc]; group
    calc y * x = x * y * c⁻¹ := by rw [this]; group
      _ = x * y * c := by rw [hci]
  have hcy := h.central c hcE y hy
  have hsq : (x * y) * (x * y) = (x * x) * (y * y) * c := by
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y * c) * y := by rw [hyx]
      _ = x * x * y * (c * y) := by group
      _ = x * x * y * (y * c) := by rw [hcy]
      _ = (x * x) * (y * y) * c := by group
  have e1 := (h.sq _ (mul_mem hx hy)).2
  rw [hsq, h.cE_mul _ (mul_mem (h.sq x hx).1 (h.sq y hy).1) _ hcE,
    h.cE_mul _ (h.sq x hx).1 _ (h.sq y hy).1, (h.sq x hx).2, (h.sq y hy).2,
    h.cV_mul x hx y hy] at e1
  unfold betaOf
  rw [← e1]
  simp [Nat.xor_comm, Nat.xor_left_comm]

theorem mem_E_of_comm {y : G} (hy : y ∈ Jh) (hc : ∀ x ∈ Jh, x * y = y * x) : y ∈ E := by
  refine (h.cV_eq_zero y hy).1 (by_contra fun hne => ?_)
  obtain ⟨w, hw, hβ⟩ := beta_radical u _ (h.cV_lt y hy) hne
  obtain ⟨x, hx, rfl⟩ := h.cV_surj w hw
  apply hβ
  rw [← h.cE_comm hy hx]
  have : y⁻¹ * x⁻¹ * y * x = 1 := by
    rw [mul_assoc (y⁻¹ * x⁻¹), ← hc x hx]; group
  rw [this, h.cE_one]

theorem conj_mem_E {g e : G} (hg : g ∈ normalizer (Jh : Set G)) (he : e ∈ E) :
    g * e * g⁻¹ ∈ E := by
  refine h.mem_E_of_comm (conj_mem_Jh hg (h.E_le he)) fun x hx => ?_
  have hx' := conj_inv_mem_Jh hg hx
  have hc := h.central e he _ hx'
  calc x * (g * e * g⁻¹) = g * ((g⁻¹ * x * g) * e) * g⁻¹ := by group
    _ = g * (e * (g⁻¹ * x * g)) * g⁻¹ := by rw [hc]
    _ = g * e * g⁻¹ * x := by group

end KillData

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
