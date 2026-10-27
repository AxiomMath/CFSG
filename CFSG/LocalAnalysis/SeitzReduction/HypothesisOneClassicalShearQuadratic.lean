module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalShear
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.SeitzReduction

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def singularSubspace (Q : QuadraticForm K V) (W : Submodule K V)
    (hWiso : ∀ x ∈ W, ∀ y ∈ W, polar Q x y = 0) : Submodule K V where
  carrier := {v | v ∈ W ∧ Q v = 0}
  add_mem' := by
    rintro x y ⟨hxW, hx⟩ ⟨hyW, hy⟩
    refine ⟨W.add_mem hxW hyW, ?_⟩
    rw [QuadraticMap.map_add Q x y, hx, hy, hWiso x hxW y hyW, add_zero, add_zero]
  zero_mem' := ⟨W.zero_mem, QuadraticMap.map_zero Q⟩
  smul_mem' := by
    rintro a x ⟨hxW, hx⟩
    exact ⟨W.smul_mem a hxW, by rw [QuadraticMap.map_smul, hx, smul_zero]⟩

theorem mem_singularSubspace {Q : QuadraticForm K V} {W : Submodule K V}
    {hWiso : ∀ x ∈ W, ∀ y ∈ W, polar Q x y = 0} {v : V} :
    v ∈ singularSubspace Q W hWiso ↔ v ∈ W ∧ Q v = 0 :=
  Iff.rfl

theorem polarBilin_isAlt [CharP K 2] (Q : QuadraticForm K V) : (polarBilin Q).IsAlt := fun x => by
  rw [polarBilin_apply_apply, polar_self, two_nsmul, CharTwo.add_self_eq_zero]

theorem polarBilin_apply_apply_of_map {F : Type*} [FunLike F V V] [AddMonoidHomClass F V V]
    {Q : QuadraticForm K V} {φ : K ≃+* K} {T : F} (hTQ : ∀ v, Q (T v) = φ (Q v)) (x y : V) :
    polarBilin Q (T x) (T y) = φ (polarBilin Q x y) := by
  rw [polarBilin_apply_apply, polarBilin_apply_apply, polar, polar, ← map_add T, hTQ, hTQ, hTQ,
    map_sub, map_sub]

theorem semilinear_shear_rigidity_quadratic [CharP K 2] (Q : QuadraticForm K V)
    {W W₀ L : Submodule K V} (hWiso : ∀ x ∈ W, ∀ y ∈ W, polar Q x y = 0)
    (hW₀ : ∀ v, v ∈ W₀ ↔ v ∈ W ∧ Q v = 0) (hW₀0 : W₀ ≠ ⊥)
    (hLW : ∃ x ∈ L, ∃ u ∈ L, polar Q x u = 1)
    {F : Type*} [FunLike F V V] [AddMonoidHomClass F V V] {φ : K ≃+* K} (T : F)
    (hT : ∀ (a : K) v, T (a • v) = φ a • T v) (hTQ : ∀ v, Q (T v) = φ (Q v))
    (hTL : ∀ v ∈ L, T v ∈ L) (hTW : ∀ v ∈ W, T v ∈ W)
    (hsh : ∀ w ∈ W₀, ∀ u ∈ L, ∃ g : V →+ V, (∀ v, T (g v) = g (T v)) ∧
      ∀ v ∈ L, g v = v + polar Q v u • w) :
    (∀ a, φ a = a) ∧ (∀ w ∈ W₀, T w = w) ∧ (∀ h ∈ W, T h - h ∈ W₀) ∧
      (∀ x ∈ L, ∀ u ∈ L, polar Q (T x) u = polar Q x u) ∧
      ∀ x, ∀ w ∈ W₀, polar Q (T x) w = polar Q x w := by
  have hTB := polarBilin_apply_apply_of_map hTQ (T := T)
  obtain ⟨hφ, hW₀1, hLL⟩ := ShearRigidity.semilinear_core (B := polarBilin Q)
    (polarBilin_isAlt Q) hLW hW₀0 T hT hTB hTL hsh
  refine ⟨hφ, hW₀1, fun h hh => (hW₀ _).2 ⟨W.sub_mem (hTW h hh) hh, ?_⟩, hLL, fun x w hw => ?_⟩
  · rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right,
      hWiso _ (hTW h hh) h hh, neg_zero, add_zero, hTQ, hφ, CharTwo.add_self_eq_zero]
  · have h := hTB x w
    rw [hW₀1 w hw, hφ] at h
    simpa only [polarBilin_apply_apply] using h

theorem semilinear_shear_rigidity_quadratic_of_fix [CharP K 2] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQn : ∀ a : V, (∀ x, polar Q x a = 0) → a = 0)
    {W W₀ L : Submodule K V} (hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, polar Q w v = 0)
    (hW2 : ∃ w₁ ∈ W₀, ∃ w₂ ∈ W₀, LinearIndependent K ![w₁, w₂])
    {F : Type*} [FunLike F V V] [AddMonoidHomClass F V V] (T : F)
    (hTQ : ∀ v, Q (T v) = Q v) (hTW : ∀ w ∈ W, T w = w)
    (hsh : ∀ w ∈ W₀, ∀ u ∈ L, ∃ g : V →+ V, (∀ v, T (g v) = g (T v)) ∧
      (∀ v ∈ L, g v = v + polar Q v u • w) ∧ ∀ v, g v - v - polar Q v w • u ∈ W) :
    (∀ v ∈ L, T v = v) ∧ (∀ v, T v - v ∈ W) ∧ ∀ v, T (T v) = v := by
  have hTB : ∀ x y, polarBilin Q (T x) (T y) = polarBilin Q x y := fun x y =>
    polarBilin_apply_apply_of_map (φ := RingEquiv.refl K) hTQ x y
  obtain ⟨hTL1, h6, hperp⟩ := ShearRigidity.shear_rigidity_of_fix (B := polarBilin Q) hQn hL hW2
    T hTB hTW hsh
  have hW := ShearRigidity.mem_iff_forall_of_perp (B := polarBilin Q) hQn (polarBilin_isAlt Q) hL
  exact ⟨hTL1, fun v => (hW _).2 (hperp v),
    apply_apply_eq_of_apply_sub K fun v => hTL1 _ (h6 v)⟩

theorem fix_of_commute_of_singular {Q : QuadraticForm K V} {W W₀ : Submodule K V}
    {F : Type*} [FunLike F V V] [AddMonoidHomClass F V V] {T : F} {N : V →+ V}
    (hNW : ∀ h ∈ W, ∃ y, N y = h) (hTN : ∀ v, T (N v) = N (T v))
    (hb : ∀ y, (∀ w ∈ W₀, polar Q y w = 0) → N y ∈ W₀ → N y = 0)
    (h1 : ∀ h ∈ W, T h - h ∈ W₀) (h2 : ∀ x, ∀ w ∈ W₀, polar Q (T x) w = polar Q x w) :
    ∀ h ∈ W, T h = h := by
  intro h hh
  obtain ⟨y, rfl⟩ := hNW h hh
  have hy : ∀ w ∈ W₀, polar Q (T y - y) w = 0 := fun w hw => by
    rw [polar_sub_left, h2 y w hw, sub_self]
  have hN : N (T y - y) = T (N y) - N y := by rw [map_sub, hTN]
  have h0 := hb _ hy (by rw [hN]; exact h1 _ hh)
  rwa [hN, sub_eq_zero] at h0

theorem semilinear_shear_rigidity_quadratic_of_commute [CharP K 2] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQn : ∀ a : V, (∀ x, polar Q x a = 0) → a = 0)
    {W W₀ L : Submodule K V} (hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, polar Q w v = 0) (hWL : W ≤ L)
    (hW₀ : ∀ v, v ∈ W₀ ↔ v ∈ W ∧ Q v = 0)
    (hW2 : ∃ w₁ ∈ W₀, ∃ w₂ ∈ W₀, LinearIndependent K ![w₁, w₂])
    (hLW : ∃ x ∈ L, ∃ u ∈ L, polar Q x u = 1)
    {N : V →+ V} (hNV : ∀ v, N v ∈ W) (hNW : ∀ h ∈ W, ∃ y, N y = h)
    (hb : ∀ y, (∀ w ∈ W₀, polar Q y w = 0) → N y ∈ W₀ → N y = 0)
    {F : Type*} [FunLike F V V] [AddMonoidHomClass F V V] {φ : K ≃+* K} (T : F)
    (hT : ∀ (a : K) v, T (a • v) = φ a • T v) (hTQ : ∀ v, Q (T v) = φ (Q v))
    (hTL : ∀ v ∈ L, T v ∈ L) (hTN : ∀ v, T (N v) = N (T v))
    (hsh : ∀ w ∈ W₀, ∀ u ∈ L, ∃ g : V →+ V, (∀ v, T (g v) = g (T v)) ∧
      (∀ v ∈ L, g v = v + polar Q v u • w) ∧ ∀ v, g v - v - polar Q v w • u ∈ W) :
    (∀ a, φ a = a) ∧ (∀ v ∈ L, T v = v) ∧ (∀ v, T v - v ∈ W) ∧ ∀ v, T (T v) = v := by
  have hWiso : ∀ x ∈ W, ∀ y ∈ W, polar Q x y = 0 := fun x hx y hy => (hL y).1 (hWL hy) x hx
  have hTW : ∀ v ∈ W, T v ∈ W := fun v hv => by
    obtain ⟨y, rfl⟩ := hNW v hv
    rw [hTN]
    exact hNV _
  obtain ⟨w₁, hw₁, w₂, hw₂, hind⟩ := hW2
  have hW₀0 : W₀ ≠ ⊥ := (Submodule.ne_bot_iff W₀).2 ⟨w₁, hw₁, by simpa using hind.ne_zero 0⟩
  obtain ⟨hφ, -, h1, -, h2⟩ := semilinear_shear_rigidity_quadratic Q hWiso hW₀ hW₀0 hLW T hT hTQ
    hTL hTW fun w hw u hu => (hsh w hw u hu).imp fun _ hg => ⟨hg.1, hg.2.1⟩
  have hTW1 := fix_of_commute_of_singular hNW hTN hb h1 h2
  obtain ⟨hTL1, hTV, hT2⟩ := semilinear_shear_rigidity_quadratic_of_fix Q hQn hL
    ⟨w₁, hw₁, w₂, hw₂, hind⟩ T (fun v => by rw [hTQ, hφ]) hTW1 hsh
  exact ⟨hφ, hTL1, hTV, hT2⟩

end CFSG.SeitzReduction
