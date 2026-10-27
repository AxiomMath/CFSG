module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Pi.Lemmas

public section

namespace CFSG.CGT.Stroth77.Core

open Function

variable {n : ℕ}

abbrev Letter (n : ℕ) : Type := Fin n × Bool

@[expose] def evalW {H : Type*} [Group H] (t : Fin n → H) : List (Letter n) → H
  | [] => 1
  | (k, true) :: w => t k * evalW t w
  | (k, false) :: w => (t k)⁻¹ * evalW t w

theorem evalW_map {H K : Type*} [Group H] [Group K] (f : H →* K) (t : Fin n → H) :
    ∀ w : List (Letter n), f (evalW t w) = evalW (fun k => f (t k)) w
  | [] => by simp [evalW]
  | (k, true) :: w => by simp [evalW, evalW_map f t w]
  | (k, false) :: w => by simp [evalW, evalW_map f t w]

@[expose] def walk {P : Type*} [Group P] (s : Fin n → P) : P → List (Letter n) → List (P × Fin n)
  | _, [] => []
  | σ, (k, true) :: w => (σ, k) :: walk s (σ * s k) w
  | σ, (k, false) :: w => (σ * (s k)⁻¹, k) :: walk s (σ * (s k)⁻¹) w

structure Ext (G P U : Type*) [Group G] [Group P] [AddCommGroup U] where
  θ : G →* P
  θ_surj : Surjective θ
  ι : Multiplicative U →* G
  ι_inj : Injective ι
  mem_range : ∀ g, θ g = 1 → ∃ u, ι u = g
  θ_ι : ∀ u, θ (ι u) = 1
  act : P → U →+ U
  conj : ∀ (g : G) (u : U), g * ι (.ofAdd u) * g⁻¹ = ι (.ofAdd (act (θ g) u))
  two : ∀ u : U, u + u = 0

namespace Ext

variable {G P U : Type*} [Group G] [Group P] [AddCommGroup U] (X : Ext G P U)

noncomputable def val (g : G) : U := (invFun X.ι g).toAdd

theorem ι_val {g : G} (hg : X.θ g = 1) : X.ι (.ofAdd (X.val g)) = g := by
  simp only [val, ofAdd_toAdd]
  exact invFun_eq (X.mem_range g hg)

include X in
theorem neg_eq (u : U) : -u = u := neg_eq_of_add_eq_zero_left (X.two u)

noncomputable def sec (σ : P) : G := (X.θ_surj σ).choose

theorem θ_sec (σ : P) : X.θ (X.sec σ) = σ := (X.θ_surj σ).choose_spec

variable {s : Fin n → P} {t : Fin n → G}

noncomputable def edgeVal (t : Fin n → G) (e : P × Fin n) : U :=
  X.val (X.sec e.1 * t e.2 * (X.sec (e.1 * X.θ (t e.2)))⁻¹)

theorem ι_edgeVal (e : P × Fin n) :
    X.ι (.ofAdd (X.edgeVal t e)) = X.sec e.1 * t e.2 * (X.sec (e.1 * X.θ (t e.2)))⁻¹ :=
  X.ι_val (by simp [θ_sec])

theorem telescope (ht : ∀ k, X.θ (t k) = s k) :
    ∀ (w : List (Letter n)) (σ : P), X.sec σ * evalW t w * (X.sec (σ * evalW s w))⁻¹ =
      X.ι (.ofAdd (((walk s σ w).map (X.edgeVal t)).sum))
  | [], σ => by simp [evalW, walk]
  | (k, true) :: w, σ => by
    have h1 := X.ι_edgeVal (t := t) (σ, k)
    have h2 := telescope ht w (σ * s k)
    simp only [ht] at h1
    simp only [evalW, walk, List.map_cons, List.sum_cons, ofAdd_add, map_mul, h1, ← h2, ← mul_assoc]
    group
  | (k, false) :: w, σ => by
    have h1 := X.ι_edgeVal (t := t) (σ * (s k)⁻¹, k)
    have h2 := telescope ht w (σ * (s k)⁻¹)
    simp only [ht, inv_mul_cancel_right] at h1
    have h4 : X.sec σ * (t k)⁻¹ * (X.sec (σ * (s k)⁻¹))⁻¹ =
        X.ι (.ofAdd (X.edgeVal t (σ * (s k)⁻¹, k))) := by
      rw [← X.neg_eq (X.edgeVal t _), ofAdd_neg, map_inv, h1]
      group
    simp only [evalW, walk, List.map_cons, List.sum_cons, ofAdd_add, map_mul, ← h4, ← h2,
      ← mul_assoc]
    group

noncomputable def relVal (t : Fin n → G) (r : List (Letter n)) : U := X.val (evalW t r)

theorem ι_relVal (ht : ∀ k, X.θ (t k) = s k) {r : List (Letter n)} (hr : evalW s r = 1) :
    X.ι (.ofAdd (X.relVal t r)) = evalW t r :=
  X.ι_val (by rw [evalW_map, show (fun k => X.θ (t k)) = s from funext ht, hr])

theorem act_relVal (ht : ∀ k, X.θ (t k) = s k) {r : List (Letter n)} (hr : evalW s r = 1)
    (σ : P) : X.act σ (X.relVal t r) = ((walk s σ r).map (X.edgeVal t)).sum := by
  have hc := X.conj (X.sec σ) (X.relVal t r)
  have h := X.telescope ht r σ
  rw [X.θ_sec] at hc
  rw [hr, mul_one] at h
  refine Multiplicative.ofAdd.injective (X.ι_inj ?_)
  rw [← hc, X.ι_relVal ht hr, h]

theorem sum_map_eq_zero_of_even [DecidableEq P] (L : List (P × Fin n)) (f : P × Fin n → U)
    (h2 : ∀ u : U, u + u = 0) (hL : ∀ e ∈ L, Even (L.count e)) : (L.map f).sum = 0 := by
  rw [Finset.sum_list_map_count]
  refine Finset.sum_eq_zero fun e he => ?_
  obtain ⟨m, hm⟩ := hL e (List.mem_toFinset.1 he)
  rw [hm, add_nsmul, ← nsmul_add, h2, nsmul_zero]

theorem sum_act_relVal_eq_zero [DecidableEq P] (ht : ∀ k, X.θ (t k) = s k)
    (C : List (P × List (Letter n))) (hC : ∀ c ∈ C, evalW s c.2 = 1)
    (hev : ∀ e ∈ C.flatMap (fun c => walk s c.1 c.2),
      Even ((C.flatMap fun c => walk s c.1 c.2).count e)) :
    (C.map fun c => X.act c.1 (X.relVal t c.2)).sum = 0 := by
  have : (C.map fun c => X.act c.1 (X.relVal t c.2)) =
      C.map fun c => ((walk s c.1 c.2).map (X.edgeVal t)).sum :=
    List.map_congr_left fun c hc => X.act_relVal ht (hC c hc) c.1
  rw [this, ← sum_map_eq_zero_of_even _ (X.edgeVal t) X.two hev, List.flatMap,
    List.map_flatten, List.sum_flatten, List.map_map, List.map_map]
  rfl

@[expose] def fox (act : P → U →+ U) (s : Fin n → P) : List (Letter n) → (Fin n → U) →+ U
  | [] => 0
  | (k, true) :: w => Pi.evalAddMonoidHom _ k + (act (s k)).comp (fox act s w)
  | (k, false) :: w => (act (s k)⁻¹).comp (-(Pi.evalAddMonoidHom _ k) + fox act s w)

@[expose] def adjust (t : Fin n → G) (u : Fin n → U) (k : Fin n) : G := X.ι (.ofAdd (u k)) * t k

theorem evalW_adjust (ht : ∀ k, X.θ (t k) = s k) (u : Fin n → U) :
    ∀ w : List (Letter n), evalW (X.adjust t u) w = X.ι (.ofAdd (fox X.act s w u)) * evalW t w
  | [] => by simp [evalW, fox]
  | (k, true) :: w => by
    have hc := X.conj (t k) (fox X.act s w u)
    rw [ht] at hc
    simp only [evalW, adjust, fox, AddMonoidHom.add_apply, Pi.evalAddMonoidHom_apply,
      AddMonoidHom.comp_apply, evalW_adjust ht u w, ofAdd_add, map_mul, ← hc]
    group
  | (k, false) :: w => by
    have hc := X.conj (t k)⁻¹ (-u k + fox X.act s w u)
    rw [map_inv, ht] at hc
    simp only [evalW, adjust, fox, AddMonoidHom.comp_apply, AddMonoidHom.add_apply,
      AddMonoidHom.neg_apply, Pi.evalAddMonoidHom_apply, evalW_adjust ht u w, ← hc, ofAdd_add,
      ofAdd_neg, map_mul, map_inv]
    group

theorem θ_adjust (ht : ∀ k, X.θ (t k) = s k) (u : Fin n → U) (k : Fin n) :
    X.θ (X.adjust t u k) = s k := by
  simp [adjust, X.θ_ι, ht]

theorem relVal_adjust (ht : ∀ k, X.θ (t k) = s k) (u : Fin n → U) {r : List (Letter n)}
    (hr : evalW s r = 1) :
    X.relVal (X.adjust t u) r = fox X.act s r u + X.relVal t r := by
  refine Multiplicative.ofAdd.injective (X.ι_inj ?_)
  rw [X.ι_relVal (X.θ_adjust ht u) hr, X.evalW_adjust ht u, ← X.ι_relVal ht hr, ofAdd_add,
    map_mul]

end Ext

end CFSG.CGT.Stroth77.Core
