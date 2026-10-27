module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.LinearAlgebra

open Module QuadraticMap

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem polarBilin_comm (q : QuadraticForm (ZMod 2) V) (x y : V) :
    polarBilin q x y = polarBilin q y x := by
  rw [polarBilin_apply_apply, polarBilin_apply_apply, polar_comm]

theorem polarBilin_map_of_invariant {q : QuadraticForm (ZMod 2) V} {g : V ≃ₗ[ZMod 2] V}
    (h : ∀ v, q (g v) = q v) (x y : V) :
    polarBilin q (g x) (g y) = polarBilin q x y := by
  rw [polarBilin_apply_apply, polarBilin_apply_apply, polar, ← map_add, h (x + y), h x, h y,
    ← polar, ← polarBilin_apply_apply]

theorem eq_zero_of_polarBilin_eq_zero_of_invariant {q : QuadraticForm (ZMod 2) V}
    {w : V ≃ₗ[ZMod 2] V} (hq : polarBilin q = 0)
    (hw2 : ∀ v, w (w v) + w v + v = 0) (hinv : ∀ v, q (w v) = q v) : q = 0 := by
  have hadd : ∀ x y : V, q (x + y) = q x + q y := by
    intro x y
    rw [QuadraticMap.map_add (⇑q) x y]
    have hp : polar q x y = 0 := by
      rw [← polarBilin_apply_apply]
      exact congrArg (fun f => f x y) hq
    rw [hp, add_zero]
  ext v
  change q v = 0
  have h : q (w (w v) + w v + v) = 0 := by rw [hw2 v, map_zero]
  rw [hadd (w (w v) + w v) v, hadd (w (w v)) (w v), hinv (w v), hinv v,
    ZModModule.add_self, zero_add] at h
  exact h

theorem eq_of_invariant_of_commutant {Γ : Set (V ≃ₗ[ZMod 2] V)} {w : V ≃ₗ[ZMod 2] V}
    (hw : w ∈ Γ) (hw2 : ∀ v, w (w v) + w v + v = 0)
    (hcomm : ∀ L : V →ₗ[ZMod 2] V, (∀ g ∈ Γ, ∀ v, L (g v) = g (L v)) →
      L = 0 ∨ L = LinearMap.id ∨ L = (w : V →ₗ[ZMod 2] V) ∨
        L = (w : V →ₗ[ZMod 2] V) ∘ₗ (w : V →ₗ[ZMod 2] V))
    {q₁ q₂ : QuadraticForm (ZMod 2) V}
    (h₁ : ∀ g ∈ Γ, ∀ v, q₁ (g v) = q₁ v) (h₂ : ∀ g ∈ Γ, ∀ v, q₂ (g v) = q₂ v)
    (hnd : (polarBilin q₁).Nondegenerate) (hq₂ : q₂ ≠ 0) : q₂ = q₁ := by
  classical
  have hB₁ : ∀ g ∈ Γ, ∀ x y, polarBilin q₁ (g x) (g y) = polarBilin q₁ x y :=
    fun g hg => polarBilin_map_of_invariant (h₁ g hg)
  have hB₂ : ∀ g ∈ Γ, ∀ x y, polarBilin q₂ (g x) (g y) = polarBilin q₂ x y :=
    fun g hg => polarBilin_map_of_invariant (h₂ g hg)
  have hsq : ∀ u, w (w u) = w u + u := by
    intro u
    have h := hw2 u
    rw [add_assoc] at h
    rw [eq_neg_of_add_eq_zero_left h, ZModModule.neg_eq_self]
  have hsum : ∀ u, u + w (w u) = w u := by
    intro u
    rw [hsq u]
    calc
      u + (w u + u) = w u + (u + u) := by abel
      _ = w u := by rw [ZModModule.add_self, add_zero]
  have hsum' : ∀ u, u + w u = w (w u) := by
    intro u
    rw [hsq u, add_comm]
  have hw3 : ∀ u, w (w (w u)) = u := by
    intro u
    have hbc : w (w u) + w u = u := by
      have h := hw2 u
      rw [eq_neg_of_add_eq_zero_left h, ZModModule.neg_eq_self]
    have h := hw2 (w u)
    rw [add_assoc] at h
    rw [eq_neg_of_add_eq_zero_left h, hbc, ZModModule.neg_eq_self]
  have hw4 : ∀ u, w (w (w (w u))) = w u := fun u => hw3 (w u)
  let L : V →ₗ[ZMod 2] V :=
    (LinearMap.BilinForm.toDual (polarBilin q₁) hnd).symm.toLinearMap ∘ₗ polarBilin q₂
  have hL : ∀ v u, polarBilin q₁ (L v) u = polarBilin q₂ v u := by
    intro v u
    exact LinearMap.BilinForm.apply_toDual_symm_apply (B := polarBilin q₁) (hB := hnd)
      (polarBilin q₂ v) u
  have hLcomm : ∀ g ∈ Γ, ∀ v, L (g v) = g (L v) := by
    intro g hg v
    apply sub_eq_zero.1
    apply hnd.1
    intro u
    obtain ⟨u', rfl⟩ := g.surjective u
    calc
      polarBilin q₁ (L (g v) - g (L v)) (g u')
          = polarBilin q₁ (L (g v)) (g u') - polarBilin q₁ (g (L v)) (g u') := by
            rw [map_sub, LinearMap.sub_apply]
      _ = polarBilin q₂ (g v) (g u') - polarBilin q₁ (L v) u' := by
            rw [hL (g v) (g u'), hB₁ g hg (L v) u']
      _ = polarBilin q₂ v u' - polarBilin q₂ v u' := by
            rw [hB₂ g hg v u', hL v u']
      _ = 0 := sub_self _
  rcases hcomm L hLcomm with hL0 | hL1 | hLw | hLw2
  ·
    have hB : polarBilin q₂ = 0 := by
      ext v u
      rw [← hL v u, hL0]
      simp
    exact absurd (eq_zero_of_polarBilin_eq_zero_of_invariant hB hw2 (h₂ w hw)) hq₂
  ·
    have hB : polarBilin q₂ = polarBilin q₁ := by
      ext v u
      rw [← hL v u, hL1]
      rfl
    have hpolf : polarBilin (q₂ - q₁) = 0 := by
      ext x y
      rw [polarBilin_apply_apply, LinearMap.zero_apply]
      have hp : polar (⇑(q₂ - q₁)) x y = polar (⇑q₂) x y - polar (⇑q₁) x y := by
        simp only [polar, QuadraticMap.sub_apply]
        abel
      rw [hp]
      have hBxy : polar q₂ x y = polar q₁ x y := by
        rw [← polarBilin_apply_apply, ← polarBilin_apply_apply, hB]
      rw [hBxy, sub_self]
      rw [LinearMap.zero_apply]
    have hf : q₂ - q₁ = 0 :=
      eq_zero_of_polarBilin_eq_zero_of_invariant hpolf hw2 (fun v => by
        rw [QuadraticMap.sub_apply, QuadraticMap.sub_apply, h₂ w hw v, h₁ w hw v])
    exact sub_eq_zero.1 hf
  ·
    have hLw' : ∀ v u, polarBilin q₁ (w v) u = polarBilin q₂ v u := by
      intro v u
      have h := hL v u
      rw [hLw] at h
      exact h
    have hsym : ∀ v u, polarBilin q₁ (w v) u = polarBilin q₁ v (w u) := by
      intro v u
      calc
        polarBilin q₁ (w v) u = polarBilin q₂ v u := hLw' v u
        _ = polarBilin q₂ u v := polarBilin_comm q₂ v u
        _ = polarBilin q₁ (w u) v := (hLw' u v).symm
        _ = polarBilin q₁ v (w u) := polarBilin_comm q₁ (w u) v
    have hstep : ∀ v u, polarBilin q₁ v u = polarBilin q₁ v (w (w u)) := by
      intro v u
      calc
        polarBilin q₁ v u = polarBilin q₁ (w v) (w u) := (hB₁ w hw v u).symm
        _ = polarBilin q₁ v (w (w u)) := hsym v (w u)
    have hzeroB : ∀ v u, polarBilin q₁ v (w u) = 0 := by
      intro v u
      have h0 : polarBilin q₁ v (u + w (w u)) = 0 := by
        rw [LinearMap.map_add, hstep v u, ZModModule.add_self]
      rwa [hsum u] at h0
    have hzero : ∀ v : V, v = 0 := fun v => hnd.1 v fun x => by
      obtain ⟨u, rfl⟩ := w.surjective x
      exact hzeroB v u
    have hq0 : q₂ = 0 := by
      ext v
      rw [hzero v]
      exact map_zero q₂
    exact absurd hq0 hq₂
  ·
    have hLw2' : ∀ v u, polarBilin q₁ (w (w v)) u = polarBilin q₂ v u := by
      intro v u
      have h := hL v u
      rw [hLw2] at h
      change polarBilin q₁ (w (w v)) u = polarBilin q₂ v u at h
      exact h
    have hsym : ∀ v u, polarBilin q₁ (w (w v)) u = polarBilin q₁ v (w (w u)) := by
      intro v u
      calc
        polarBilin q₁ (w (w v)) u = polarBilin q₂ v u := hLw2' v u
        _ = polarBilin q₂ u v := polarBilin_comm q₂ v u
        _ = polarBilin q₁ (w (w u)) v := (hLw2' u v).symm
        _ = polarBilin q₁ v (w (w u)) := polarBilin_comm q₁ (w (w u)) v
    have hstep : ∀ v u, polarBilin q₁ v u = polarBilin q₁ v (w u) := by
      intro v u
      have h2 : polarBilin q₁ (w (w v)) (w (w u)) = polarBilin q₁ v u := by
        rw [hB₁ w hw (w v) (w u), hB₁ w hw v u]
      calc
        polarBilin q₁ v u = polarBilin q₁ (w (w v)) (w (w u)) := h2.symm
        _ = polarBilin q₁ v (w (w (w (w u)))) := hsym v (w (w u))
        _ = polarBilin q₁ v (w u) := by rw [hw4 u]
    have hzeroB : ∀ v u, polarBilin q₁ v (w (w u)) = 0 := by
      intro v u
      have h0 : polarBilin q₁ v (u + w u) = 0 := by
        rw [LinearMap.map_add, hstep v u, ZModModule.add_self]
      rwa [hsum' u] at h0
    have hzero : ∀ v : V, v = 0 := fun v => hnd.1 v fun x => by
      obtain ⟨u, rfl⟩ := w.surjective x
      obtain ⟨u', rfl⟩ := w.surjective u
      exact hzeroB v u'
    have hq0 : q₂ = 0 := by
      ext v
      rw [hzero v]
      exact map_zero q₂
    exact absurd hq0 hq₂
