module

public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26MCDiag

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {Y : Type*} [Group Y] [Finite Y] {K E : Subgroup Y}

theorem mc_conj_inj (e : Y) {H H' : Subgroup Y} (h : GLBConj e H = GLBConj e H') : H = H' := by
  have := congrArg (GLBConj e⁻¹) h
  rwa [mc_conj_conj, mc_conj_conj, mul_inv_cancel, gLBConj_one, gLBConj_one] at this

theorem mc_conj_comm (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {a b : Y} (ha : a ∈ E)
    (hb : b ∈ E) (H : Subgroup Y) : GLBConj a (GLBConj b H) = GLBConj b (GLBConj a H) := by
  rw [mc_conj_conj, mc_conj_conj, hEc b hb a ha]

theorem mc_conj_eq_iff (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {e f : Y} (he : e ∈ E)
    (hf : f ∈ E) : GLBConj f (GLBConj e K) = GLBConj e K ↔ GLBConj f K = K := by
  rw [mc_conj_comm hEc hf he]
  constructor
  · intro h
    exact mc_conj_inj e h
  · intro h
    rw [h]

theorem mc_moves (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {e g : Y} (he : e ∈ E) (hg : g ∈ E)
    (hgK : GLBConj g K ≠ K) : GLBConj g (GLBConj e K) ≠ GLBConj e K :=
  fun h => hgK ((mc_conj_eq_iff hEc he hg).1 h)

theorem mc_conj_inv_self {H : Subgroup Y} {h : Y} (hh : GLBConj h H = H) :
    GLBConj h⁻¹ H = H := by
  have := congrArg (GLBConj h⁻¹) hh
  rw [mc_conj_conj, mul_inv_cancel, gLBConj_one] at this
  exact this.symm

theorem mc_ne_of_moves (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {e f f' : Y} (he : e ∈ E)
    (hf : f ∈ E) (hf' : f' ∈ E) (h : GLBConj (f * f'⁻¹) K ≠ K) :
    GLBConj f (GLBConj e K) ≠ GLBConj f' (GLBConj e K) := by
  intro heq
  apply h
  have h1 := congrArg (GLBConj f'⁻¹) heq
  rw [mc_conj_conj f'⁻¹ f (GLBConj e K), mc_conj_conj f'⁻¹ f' (GLBConj e K), mul_inv_cancel,
    gLBConj_one] at h1
  exact (mc_conj_eq_iff hEc he (E.mul_mem hf (E.inv_mem hf'))).1 h1

theorem mc_faith_conj (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hfaith : ∀ e ∈ E, (∀ k ∈ K, e * k = k * e) → e = 1) {j : Y} (hj : j ∈ E) :
    ∀ e ∈ E, (∀ k ∈ GLBConj j K, e * k = k * e) → e = 1 := by
  intro e he hcomm
  apply hfaith e he
  intro k hk
  have h1 : e * (j⁻¹ * k * j) = (j⁻¹ * k * j) * e := hcomm _ (mc_mem_conj hk)
  have hej : e * j = j * e := hEc e he j hj
  have hej' : e * j⁻¹ = j⁻¹ * e := (Commute.inv_right (show Commute e j from hej)).eq
  calc e * k = e * (j * (j⁻¹ * k * j) * j⁻¹) := by group
    _ = (e * j) * (j⁻¹ * k * j) * j⁻¹ := by group
    _ = j * e * (j⁻¹ * k * j) * j⁻¹ := by rw [hej]
    _ = j * (e * (j⁻¹ * k * j)) * j⁻¹ := by group
    _ = j * ((j⁻¹ * k * j) * e) * j⁻¹ := by rw [h1]
    _ = (j * (j⁻¹ * k * j)) * (e * j⁻¹) := by group
    _ = (j * (j⁻¹ * k * j)) * (j⁻¹ * e) := by rw [hej']
    _ = k * e := by group

theorem mc_normalizes (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {e h : Y} (he : e ∈ E)
    (hh : h ∈ E) (hhK : GLBConj h K = K) : ∀ u ∈ GLBConj e K, h⁻¹ * u * h ∈ GLBConj e K := by
  intro u hu
  have h1 : GLBConj h (GLBConj e K) = GLBConj e K := (mc_conj_eq_iff hEc he hh).2 hhK
  have h2 : h⁻¹ * u * h ∈ GLBConj h (GLBConj e K) := mc_mem_conj hu
  rwa [h1] at h2

end CFSG.HardMathSupport.Solomon.Coordinator
