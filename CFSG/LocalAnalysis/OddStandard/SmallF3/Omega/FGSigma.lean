module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGCplx
import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.BilinearForm.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

private lemma pi_selfadj (a b l d sx tx sy ty : ZMod 3) :
    d * (l * a * sx - b * tx) * sy + d * (a * tx - b * sx) * ty
      = d * (l * a * sy - b * ty) * sx + d * (a * ty - b * sy) * tx := by
  ring

private lemma pi_s : ∀ a b l d s t : ZMod 3, a ≠ 0 → (l = 1 ∨ l = -1) → (l = 1 → b = 0) →
    d = l * a ^ 2 - b ^ 2 →
    d * (l * a * s - b * t) * a + d * (a * t - b * s) * b = s := by
  decide

private lemma pi_t : ∀ a b l d s t : ZMod 3, a ≠ 0 → (l = 1 ∨ l = -1) → (l = 1 → b = 0) →
    d = l * a ^ 2 - b ^ 2 →
    d * (l * a * s - b * t) * b + d * (a * t - b * s) * (l * a) = t := by
  decide

private lemma pi_comm_X : ∀ a b l d s t : ZMod 3, a ≠ 0 → (l = 1 ∨ l = -1) → (l = 1 → b = 0) →
    d = l * a ^ 2 - b ^ 2 →
    d * (l * a * ((-l) * t) - b * (l * s)) = -(d * (a * t - b * s)) := by
  decide

private lemma pi_comm_Y : ∀ a b l d s t : ZMod 3, a ≠ 0 → (l = 1 ∨ l = -1) → (l = 1 → b = 0) →
    d = l * a ^ 2 - b ^ 2 →
    d * (a * (l * s) - b * ((-l) * t)) = d * (l * a * s - b * t) := by
  decide

private lemma pi_ne_zero : ∀ a b l d s t : ZMod 3, a ≠ 0 → (l = 1 ∨ l = -1) →
    (l = 1 → b = 0) → d = l * a ^ 2 - b ^ 2 → s ≠ 0 →
    d * (l * a * s - b * t) ≠ 0 ∨ d * (a * t - b * s) ≠ 0 := by
  decide

theorem fg_exists_sigma {B : LinearMap.BilinForm (ZMod 3) V} {ρ : V →ₗ[ZMod 3] V} {lam : ZMod 3}
    (h : FGCplx B ρ lam) {v : V} (hv : B v v ≠ 0) :
    ∃ σ : V ≃ₗ[ZMod 3] V, (∀ x y, B (σ x) (σ y) = B x y) ∧ (∀ x, σ (ρ x) = ρ (σ x)) ∧
      ∀ y, B y v ≠ 0 → ∃ m₁ m₂ : ZMod 3, (m₁ ≠ 0 ∨ m₂ ≠ 0) ∧ σ y - y = m₁ • v + m₂ • ρ v := by
  set a : ZMod 3 := B v v with ha
  set b : ZMod 3 := B v (ρ v) with hb
  set d : ZMod 3 := lam * a ^ 2 - b ^ 2 with hd
  have ha0 : a ≠ 0 := hv
  have hb_lam1 : lam = 1 → b = 0 := by
    intro hl
    rw [hb, h.pair_zero hl v]
  have hbb : B (ρ v) (ρ v) = lam * a := by
    rw [h.isom v v, ← ha]
  have hbρv : B (ρ v) v = b := by
    rw [h.symm (ρ v) v, ← hb]
  let sL : V →ₗ[ZMod 3] (ZMod 3) := B.flip v
  let tL : V →ₗ[ZMod 3] (ZMod 3) := B.flip (ρ v)
  let fX : V →ₗ[ZMod 3] (ZMod 3) := d • ((lam * a) • sL - b • tL)
  let fY : V →ₗ[ZMod 3] (ZMod 3) := d • (a • tL - b • sL)
  let π : V →ₗ[ZMod 3] V := fX.smulRight v + fY.smulRight (ρ v)
  have hπ : ∀ u : V, π u = (d * (lam * a * B u v - b * B u (ρ v))) • v
                          + (d * (a * B u (ρ v) - b * B u v)) • ρ v := fun _ => rfl
  have hBπv : ∀ u : V, B (π u) v = B u v := by
    intro u
    rw [hπ u]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [← ha, hbρv]
    exact pi_s a b lam d (B u v) (B u (ρ v)) ha0 h.lam_eq hb_lam1 hd
  have hBπρv : ∀ u : V, B (π u) (ρ v) = B u (ρ v) := by
    intro u
    rw [hπ u]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [← hb, hbb]
    exact pi_t a b lam d (B u v) (B u (ρ v)) ha0 h.lam_eq hb_lam1 hd
  have hBπxπy : ∀ x y : V, B (π x) (π y) = B x (π y) := by
    intro x y
    rw [hπ y]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hBπv x, hBπρv x]
  have hself : ∀ x y : V, B (π x) y = B x (π y) := by
    intro x y
    rw [hπ x, hπ y]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [h.symm v y, h.symm (ρ v) y]
    exact pi_selfadj a b lam d (B x v) (B x (ρ v)) (B y v) (B y (ρ v))
  have hππ : ∀ u : V, π (π u) = π u := by
    intro u
    rw [hπ (π u), hBπv u, hBπρv u, hπ u]
  let σlin : V →ₗ[ZMod 3] V := LinearMap.id + π
  have hσinv : Function.Involutive σlin := by
    intro u
    change (u + π u) + π (u + π u) = u
    rw [map_add, hππ]
    have h3sum : π u + π u + π u = (3 : ZMod 3) • π u := by
      rw [show (3 : ZMod 3) = 1 + 1 + 1 by decide]
      simp only [add_smul, one_smul]
    rw [show (u + π u) + (π u + π u) = u + (π u + π u + π u) by abel, h3sum,
      show (3 : ZMod 3) = 0 by decide, zero_smul, add_zero]
  let σ : V ≃ₗ[ZMod 3] V := LinearEquiv.ofInvolutive σlin hσinv
  have hσ : ∀ u : V, σ u = u + π u := fun _ => rfl
  have hisom : ∀ x y : V, B (σ x) (σ y) = B x y := by
    intro x y
    rw [hσ x, hσ y]
    have e1 : B (x + π x) (y + π y)
        = B x y + B x (π y) + B (π x) y + B (π x) (π y) := by
      simp only [map_add, LinearMap.add_apply]
      abel
    rw [e1, hBπxπy x y, hself x y]
    have hsum : B x (π y) + B x (π y) + B x (π y) = 0 := by
      have h3' : B x (π y) + B x (π y) + B x (π y) = (3 : ZMod 3) • B x (π y) := by
        rw [show (3 : ZMod 3) = 1 + 1 + 1 by decide]
        simp only [add_smul, one_smul]
      rw [h3', show (3 : ZMod 3) = 0 by decide, zero_smul]
    rw [show B x y + B x (π y) + B x (π y) + B x (π y)
          = B x y + (B x (π y) + B x (π y) + B x (π y)) by abel, hsum, add_zero]
  have hcomm : ∀ x : V, σ (ρ x) = ρ (σ x) := by
    intro x
    rw [hσ (ρ x), hσ x, map_add]
    congr 1
    have hX := pi_comm_X a b lam d (B x v) (B x (ρ v)) ha0 h.lam_eq hb_lam1 hd
    have hY := pi_comm_Y a b lam d (B x v) (B x (ρ v)) ha0 h.lam_eq hb_lam1 hd
    rw [hπ (ρ x), h.adj x v, h.isom x v, hπ x, map_add, map_smul, map_smul, h.sq v,
      hX, hY, smul_neg, ← neg_smul]
    abel
  refine ⟨σ, hisom, hcomm, ?_⟩
  intro y hyv
  refine ⟨d * (lam * a * B y v - b * B y (ρ v)), d * (a * B y (ρ v) - b * B y v), ?_, ?_⟩
  · exact pi_ne_zero a b lam d (B y v) (B y (ρ v)) ha0 h.lam_eq hb_lam1 hd hyv
  · rw [hσ y, hπ y]
    abel

end CFSG.OddStandard.SmallF3.Omega
