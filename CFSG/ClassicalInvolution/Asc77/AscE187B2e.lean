module

public import CFSG.ClassicalInvolution.ModelFacts.LinearAutLift
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

theorem core4 {u ut u' u't z zt t y : G} (hu2 : u * u = z) (hut2 : ut * ut = zt)
    (hu'2 : u' * u' = z) (hu't2 : u't * u't = zt) (huut : u * ut = ut * u) (huu' : u * u' = u' * u)
    (huu't : u * u't = u't * u) (hutu' : ut * u' = u' * ut) (hutu't : ut * u't = u't * ut)
    (hu'u't : u' * u't = u't * u') {b : G} (hb : b = z * zt) (hb2 : b * b = 1)
    (ht1 : t * u * t⁻¹ = ut) (ht2 : t * ut * t⁻¹ = u) (ht3 : t * u' * t⁻¹ = u't)
    (ht4 : t * u't * t⁻¹ = u') (hy1 : y * u ≠ u * y) (hy2 : y * ut = ut * y)
    (hy3 : y * u' = u' * y) (hy4 : y * u't = u't * y) :
    (((u * ut) * (u' * u't)⁻¹) * ((u * ut) * (u' * u't)⁻¹) = 1) ∧
      ((u * ut) * (u' * u't)⁻¹ ≠ 1) ∧ ((u * ut) * (u' * u't)⁻¹ ≠ b) ∧
      ((u * ut) * (u' * u't)⁻¹) * b = b * ((u * ut) * (u' * u't)⁻¹) ∧
      t * ((u * ut) * (u' * u't)⁻¹) * t⁻¹ = (u * ut) * (u' * u't)⁻¹ := by
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = u * ut := ⟨_, rfl⟩
  obtain ⟨ξ', hξ'⟩ : ∃ ξ', ξ' = u' * u't := ⟨_, rfl⟩
  rw [← hξ, ← hξ']
  have hξξ : ξ * ξ = b := by
    calc ξ * ξ = (u * u) * (ut * ut) := by
          rw [hξ]
          calc u * ut * (u * ut) = u * (ut * u) * ut := by group
            _ = u * (u * ut) * ut := by rw [huut]
            _ = (u * u) * (ut * ut) := by group
      _ = b := by rw [hu2, hut2, hb]
  have hξ'ξ' : ξ' * ξ' = b := by
    calc ξ' * ξ' = (u' * u') * (u't * u't) := by
          rw [hξ']
          calc u' * u't * (u' * u't) = u' * (u't * u') * u't := by group
            _ = u' * (u' * u't) * u't := by rw [hu'u't]
            _ = (u' * u') * (u't * u't) := by group
      _ = b := by rw [hu'2, hu't2, hb]
  have hcomm : ξ * ξ' = ξ' * ξ := by
    rw [hξ, hξ']
    have c1 : Commute u u' := huu'
    have c2 : Commute u u't := huu't
    have c3 : Commute ut u' := hutu'
    have c4 : Commute ut u't := hutu't
    exact ((c1.mul_right c2).mul_left (c3.mul_right c4)).eq
  have hξ'inv : ξ'⁻¹ * ξ'⁻¹ = b := by
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    rw [← mul_inv_rev, hξ'ξ', hbi]
  have hξb : ξ * b = b * ξ := by rw [← hξξ]; group
  have hξ'b : ξ' * b = b * ξ' := by rw [← hξ'ξ']; group
  have hξξ'inv : ξ * ξ'⁻¹ = ξ'⁻¹ * ξ := (Commute.inv_right (show Commute ξ ξ' from hcomm)).eq
  have hee : (ξ * ξ'⁻¹) * (ξ * ξ'⁻¹) = 1 := by
    calc (ξ * ξ'⁻¹) * (ξ * ξ'⁻¹) = ξ * (ξ'⁻¹ * ξ) * ξ'⁻¹ := by group
      _ = ξ * (ξ * ξ'⁻¹) * ξ'⁻¹ := by rw [hξξ'inv]
      _ = (ξ * ξ) * (ξ'⁻¹ * ξ'⁻¹) := by group
      _ = b * b := by rw [hξξ, hξ'inv]
      _ = 1 := hb2
  have hyξ' : y * ξ' = ξ' * y := by
    rw [hξ']
    calc y * (u' * u't) = (y * u') * u't := by group
      _ = u' * (y * u't) := by rw [hy3]; group
      _ = u' * (u't * y) := by rw [hy4]
      _ = (u' * u't) * y := by group
  have hyξ'inv : y * ξ'⁻¹ = ξ'⁻¹ * y := (Commute.inv_right (show Commute y ξ' from hyξ')).eq
  have hyξ : ∀ x, (x = ξ' ∨ x = ξ'⁻¹) → x = ξ → False := by
    intro x hx hxξ
    have hyx : y * x = x * y := by rcases hx with rfl | rfl <;> assumption
    rw [hxξ] at hyx
    apply hy1
    rw [hξ] at hyx
    have : y * u * ut = u * y * ut := by
      calc y * u * ut = y * (u * ut) := by group
        _ = (u * ut) * y := hyx
        _ = u * (ut * y) := by group
        _ = u * (y * ut) := by rw [hy2]
        _ = u * y * ut := by group
    exact mul_right_cancel this
  refine ⟨hee, ?_, ?_, ?_, ?_⟩
  · intro h1
    have : ξ = ξ' := by
      calc ξ = (ξ * ξ'⁻¹) * ξ' := by group
        _ = ξ' := by rw [h1, one_mul]
    exact hyξ ξ' (Or.inl rfl) this.symm
  · intro h1
    have : ξ = ξ'⁻¹ := by
      calc ξ = (ξ * ξ'⁻¹) * ξ' := by group
        _ = b * ξ' := by rw [h1]
        _ = ξ'⁻¹ := by
          have h4 : (ξ' * ξ') * (ξ' * ξ') = 1 := by rw [hξ'ξ', hb2]
          calc b * ξ' = (ξ' * ξ') * ξ' := by rw [hξ'ξ']
            _ = ξ'⁻¹ * ((ξ' * ξ') * (ξ' * ξ')) := by group
            _ = ξ'⁻¹ := by rw [h4, mul_one]
    exact hyξ ξ'⁻¹ (Or.inr rfl) this.symm
  · calc (ξ * ξ'⁻¹) * b = ξ * (ξ'⁻¹ * b) := by group
      _ = ξ * (b * ξ'⁻¹) := by rw [(Commute.inv_left (show Commute ξ' b from hξ'b)).eq]
      _ = (ξ * b) * ξ'⁻¹ := by group
      _ = (b * ξ) * ξ'⁻¹ := by rw [hξb]
      _ = b * (ξ * ξ'⁻¹) := by group
  · have e1 : t * ξ * t⁻¹ = ξ := by
      calc t * ξ * t⁻¹ = (t * u * t⁻¹) * (t * ut * t⁻¹) := by rw [hξ]; group
        _ = ut * u := by rw [ht1, ht2]
        _ = ξ := by rw [hξ, huut]
    have e2 : t * ξ' * t⁻¹ = ξ' := by
      calc t * ξ' * t⁻¹ = (t * u' * t⁻¹) * (t * u't * t⁻¹) := by rw [hξ']; group
        _ = u't * u' := by rw [ht3, ht4]
        _ = ξ' := by rw [hξ', hu'u't]
    calc t * (ξ * ξ'⁻¹) * t⁻¹ = (t * ξ * t⁻¹) * (t * ξ' * t⁻¹)⁻¹ := by group
      _ = ξ * ξ'⁻¹ := by rw [e1, e2]

end CFSG.ClassicalInvolution.Asc77
