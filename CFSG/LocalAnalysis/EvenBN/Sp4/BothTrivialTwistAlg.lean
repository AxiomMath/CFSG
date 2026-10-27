module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Equiv.Defs

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwist

section Fpf

variable {V : Type*} [CommGroup V]

theorem apply_apply_eq_of_fpf (hV : ∀ v : V, v * v = 1) {f : V ≃* V}
    (h3 : ∀ v, f (f (f v)) = v) (hf : ∀ v, f v = v → v = 1) (v : V) : f (f v) = v * f v := by
  have h1 : v * f v * f (f v) = 1 := by
    refine hf _ ?_
    rw [map_mul, map_mul, h3]
    ac_rfl
  have h2 : f (f v) = (v * f v)⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [h2]
  exact inv_eq_of_mul_eq_one_right (hV _)

theorem eq_of_fpf (hV : ∀ v : V, v * v = 1) {f g : V ≃* V}
    (hf3 : ∀ v, f (f (f v)) = v) (hg3 : ∀ v, g (g (g v)) = v) (hfg : ∀ v, f (g v) = g (f v))
    (hf : ∀ v, f v = v → v = 1) (hg : ∀ v, g v = v → v = 1)
    (hh : ∀ v, f (g v) = v → v = 1) (v : V) : f v = g v := by
  have F1 := apply_apply_eq_of_fpf hV hf3 hf
  have G1 := apply_apply_eq_of_fpf hV hg3 hg
  let h : V ≃* V := g.trans f
  have hhv : ∀ v, h v = f (g v) := fun v => rfl
  have hgf : ∀ x, g (f x) = f (g x) := fun x => (hfg x).symm
  have hff : ∀ x, g (f (f x)) = f (f (g x)) := fun x => by rw [hgf, hgf]
  have hh3 : ∀ v, h (h (h v)) = v := by
    intro v
    simp only [hhv]
    rw [hgf (g v), hff (g (g v)), hg3 v, hf3 v]
  have H1 := apply_apply_eq_of_fpf hV hh3 (fun v hv => hh v hv) v
  simp only [hhv] at H1
  rw [hgf (g v), G1 v] at H1
  simp only [map_mul] at H1
  rw [F1 v, F1 (g v)] at H1
  have h2 : (v * f (g v)) * (f v * g v) = (v * f (g v)) * 1 := by
    calc (v * f (g v)) * (f v * g v) = (v * f v) * (g v * f (g v)) := by ac_rfl
      _ = v * f (g v) := H1
      _ = (v * f (g v)) * 1 := (mul_one _).symm
  have h3 : f v * g v = 1 := mul_left_cancel h2
  have h4 : g v = (f v)⁻¹ := eq_inv_of_mul_eq_one_right h3
  rw [h4]
  exact (inv_eq_of_mul_eq_one_right (hV (f v))).symm

end Fpf

section Core

variable {V₂ V₁ M : Type*} [CommGroup V₂] [CommGroup V₁] [CommGroup M]

theorem core_false [Finite V₁] (hV₂ : ∀ v : V₂, v * v = 1)
    (f₂ g₂ : V₂ ≃* V₂) (f₁ g₁ : V₁ ≃* V₁) (fM gM : M ≃* M)
    (hf₂ : ∀ v, f₂ (f₂ (f₂ v)) = v) (hg₂ : ∀ v, g₂ (g₂ (g₂ v)) = v)
    (hc₂ : ∀ v, f₂ (g₂ v) = g₂ (f₂ v)) (hc₁ : ∀ v, f₁ (g₁ v) = g₁ (f₁ v))
    (p : V₂ → V₁ → M)
    (hpf : ∀ v w, fM (p v w) = p (f₂ v) (f₁ w)) (hpg : ∀ v w, gM (p v w) = p (g₂ v) (g₁ w))
    (hp₂ : ∀ v w w', p v (w * w') = p v w * p v w')
    (hns : ∀ v w, p v w = 1 → v = 1 ∨ w = 1)
    (σ : V₂ ≃* V₁) (hσf : ∀ v, σ (f₂ v) = g₁ (σ v)) (hσg : ∀ v, σ (g₂ v) = f₁ (σ v))
    (hfpf₂ : ∀ v, f₂ v = v → v = 1)
    (hMf : ∀ m, fM m = m → m = 1) (hMg : ∀ m, gM m = m)
    (v₀ : V₂) (hv₀ : v₀ ≠ 1) : False := by
  have hp1 : ∀ v, p v 1 = 1 := fun v => by
    have h : p v 1 = p v 1 * p v 1 := by rw [← hp₂, mul_one]
    exact mul_left_cancel (a := p v 1) (by rw [mul_one]; exact h.symm)
  have hpinv : ∀ v w, p v w⁻¹ = (p v w)⁻¹ := fun v w => by
    have h := hp₂ v w w⁻¹
    rw [mul_inv_cancel, hp1] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hg₁ : ∀ w, g₁ w = w → w = 1 := fun w hw => by
    obtain ⟨x, rfl⟩ := σ.surjective w
    have h1 : σ (f₂ x) = σ x := by rw [hσf]; exact hw
    rw [hfpf₂ x (σ.injective h1), map_one]
  have hg : ∀ v, g₂ v = v → v = 1 := fun v hv => by
    by_contra hv1
    have hinj : Function.Injective (fun w : V₁ => g₁ w * w⁻¹) := by
      intro a b hab
      have h1 : g₁ (a * b⁻¹) = a * b⁻¹ := by
        have h2 : g₁ a * a⁻¹ = g₁ b * b⁻¹ := hab
        rw [map_mul, map_inv]
        have h3 : g₁ a * (g₁ b)⁻¹ * (a * b⁻¹)⁻¹ = (g₁ a * a⁻¹) * (g₁ b * b⁻¹)⁻¹ := by
          simp only [mul_inv_rev, inv_inv, mul_assoc, mul_comm, mul_left_comm]
        rw [← h2, mul_inv_cancel] at h3
        exact mul_inv_eq_one.mp h3
      exact mul_inv_eq_one.mp (hg₁ _ h1)
    obtain ⟨w₀, hw₀⟩ := (Finite.injective_iff_surjective.mp hinj) (σ v₀)
    have hpv : p v (σ v₀) = 1 := by
      rw [← hw₀]
      have h2 : p v (g₁ w₀) = p v w₀ := by
        have := hpg v w₀
        rw [hMg, hv] at this
        exact this.symm
      show p v (g₁ w₀ * w₀⁻¹) = 1
      rw [hp₂, h2, hpinv, mul_inv_cancel]
    rcases hns v (σ v₀) hpv with h | h
    · exact hv1 h
    · exact hv₀ ((σ.map_eq_one_iff).mp h)
  have hh : ∀ v, f₂ (g₂ v) = v → v = 1 := fun v hv => by
    have h1 : f₁ (g₁ (σ v)) = σ v := by
      have h0 := hσf (g₂ v)
      rw [hv, hσg] at h0
      rw [hc₁]
      exact h0.symm
    have h2 : fM (p v (σ v)) = p v (σ v) := by
      have h3 := hpg v (σ v)
      rw [hMg] at h3
      calc fM (p v (σ v)) = fM (p (g₂ v) (g₁ (σ v))) := by rw [← h3]
        _ = p (f₂ (g₂ v)) (f₁ (g₁ (σ v))) := hpf _ _
        _ = p v (σ v) := by rw [hv, h1]
    rcases hns v (σ v) (hMf _ h2) with h4 | h4
    · exact h4
    · exact (σ.map_eq_one_iff).mp h4
  have hfg : ∀ v, f₂ v = g₂ v := eq_of_fpf hV₂ hf₂ hg₂ hc₂ hfpf₂ hg hh
  have hfg₁ : ∀ w, f₁ w = g₁ w := fun w => by
    obtain ⟨v, rfl⟩ := σ.surjective w
    rw [← hσg, ← hσf, hfg]
  have hp1' : ∀ v w, p v w = 1 := fun v w => by
    refine hMf _ ?_
    calc fM (p v w) = p (f₂ v) (f₁ w) := hpf v w
      _ = p (g₂ v) (g₁ w) := by rw [hfg v, hfg₁ w]
      _ = gM (p v w) := (hpg v w).symm
      _ = p v w := hMg _
  have h5 : σ v₀ = 1 := by
    rcases hns v₀ (σ v₀) (hp1' _ _) with h | h
    · exact absurd h hv₀
    · exact h
  exact hv₀ ((σ.map_eq_one_iff).mp h5)

end Core

section CoreGroup

variable {V₂ V₁ M : Type*} [Group V₂] [Group V₁] [Group M]

theorem core_false_of_comm [Finite V₁] (hab₂ : ∀ a b : V₂, a * b = b * a)
    (hab₁ : ∀ a b : V₁, a * b = b * a) (habM : ∀ a b : M, a * b = b * a)
    (hV₂ : ∀ v : V₂, v * v = 1)
    (f₂ g₂ : V₂ ≃* V₂) (f₁ g₁ : V₁ ≃* V₁) (fM gM : M ≃* M)
    (hf₂ : ∀ v, f₂ (f₂ (f₂ v)) = v) (hg₂ : ∀ v, g₂ (g₂ (g₂ v)) = v)
    (hc₂ : ∀ v, f₂ (g₂ v) = g₂ (f₂ v)) (hc₁ : ∀ v, f₁ (g₁ v) = g₁ (f₁ v))
    (p : V₂ → V₁ → M)
    (hpf : ∀ v w, fM (p v w) = p (f₂ v) (f₁ w)) (hpg : ∀ v w, gM (p v w) = p (g₂ v) (g₁ w))
    (hp₂ : ∀ v w w', p v (w * w') = p v w * p v w')
    (hns : ∀ v w, p v w = 1 → v = 1 ∨ w = 1)
    (σ : V₂ ≃* V₁) (hσf : ∀ v, σ (f₂ v) = g₁ (σ v)) (hσg : ∀ v, σ (g₂ v) = f₁ (σ v))
    (hfpf₂ : ∀ v, f₂ v = v → v = 1)
    (hMf : ∀ m, fM m = m → m = 1) (hMg : ∀ m, gM m = m)
    (v₀ : V₂) (hv₀ : v₀ ≠ 1) : False := by
  letI : CommGroup V₂ := { (inferInstance : Group V₂) with mul_comm := hab₂ }
  letI : CommGroup V₁ := { (inferInstance : Group V₁) with mul_comm := hab₁ }
  letI : CommGroup M := { (inferInstance : Group M) with mul_comm := habM }
  exact core_false hV₂ f₂ g₂ f₁ g₁ fM gM hf₂ hg₂ hc₂ hc₁ p hpf hpg hp₂ hns σ hσf hσg hfpf₂ hMf
    hMg v₀ hv₀

end CoreGroup

end CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwist
