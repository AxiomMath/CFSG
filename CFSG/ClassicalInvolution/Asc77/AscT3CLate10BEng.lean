module

public import CFSG.ClassicalInvolution.Asc77.AscT3CLate9CEng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII


open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20G.late_swap_sq_data (d : Std20G K K' J S R R' W V z t) {σ e : G}
    (hσ : σ ∈ (S : Subgroup G)) (hσK : conjSub σ K = K') (hσ2 : σ * σ ∈ W)
    (heKW : e ∈ K ⊓ W) (he2 : e * e = z) :
    (e * (σ * e * σ⁻¹) = t ∨ e * (σ * e * σ⁻¹) = z * t) ∧ σ * t * σ⁻¹ = t := by
  have hWc := d.late_hWc
  have hz1 : z ≠ 1 := d.viol.hzK.ne_one
  have hσz := d.late_S_act_z hσ
  have hconjW : ∀ w ∈ W, σ * w * σ⁻¹ ∈ W := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp (d.hWN hσ) w).mp hw
  have heW : e ∈ W := heKW.2
  have heK' : e ∉ K' := by
    intro heK'
    have hA2 : IsPGroup 2 ↥(Subgroup.zpowers e) :=
      S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (d.hWS heW))
    have hcard := Sec6Gen.card_le_two_of_le_inf d.late_hΩ d.late_mem_K d.late_mem_K' d.ne.symm hA2
      (Subgroup.zpowers_le.mpr heKW.1) (Subgroup.zpowers_le.mpr heK')
    rw [Nat.card_zpowers] at hcard
    have hpos : 0 < orderOf e := by
      rw [← Nat.card_zpowers]
      exact Nat.card_pos
    have hsq : e * e = 1 := by
      rcases (by omega : orderOf e = 1 ∨ orderOf e = 2) with h | h
      · rw [orderOf_eq_one_iff.mp h, one_mul]
      · rw [← pow_two, ← h, pow_orderOf_eq_one]
    exact hz1 (he2.symm.trans hsq)
  have heσK' : σ * e * σ⁻¹ ∈ K' := hσK ▸ conj_mem_conjSub heKW.1
  have heσW : σ * e * σ⁻¹ ∈ W := hconjW e heW
  have heσ2 : (σ * e * σ⁻¹) * (σ * e * σ⁻¹) = z := by
    calc (σ * e * σ⁻¹) * (σ * e * σ⁻¹) = σ * (e * e) * σ⁻¹ := by group
      _ = σ * z * σ⁻¹ := by rw [he2]
      _ = z := hσz
  have ha₀W : e * (σ * e * σ⁻¹) ∈ W := W.mul_mem heW heσW
  have ha₀2 : (e * (σ * e * σ⁻¹)) * (e * (σ * e * σ⁻¹)) = 1 := by
    calc (e * (σ * e * σ⁻¹)) * (e * (σ * e * σ⁻¹))
        = e * ((σ * e * σ⁻¹) * e) * (σ * e * σ⁻¹) := by group
      _ = e * (e * (σ * e * σ⁻¹)) * (σ * e * σ⁻¹) := by rw [hWc _ heσW _ heW]
      _ = (e * e) * ((σ * e * σ⁻¹) * (σ * e * σ⁻¹)) := by group
      _ = z * z := by rw [he2, heσ2]
      _ = 1 := d.viol.hzK.sq
  have ha₀1 : e * (σ * e * σ⁻¹) ≠ 1 := by
    intro h
    apply heK'
    have : σ * e * σ⁻¹ = e⁻¹ := eq_inv_of_mul_eq_one_right h
    have h2 : e = (σ * e * σ⁻¹)⁻¹ := by rw [this, inv_inv]
    rw [h2]
    exact K'.inv_mem heσK'
  have ha₀z : e * (σ * e * σ⁻¹) ≠ z := by
    intro h
    apply heK'
    have h1 : σ * e * σ⁻¹ = e := by
      apply mul_left_cancel (a := e)
      rw [h, ← he2]
    rw [← h1]
    exact heσK'
  have hfix : σ * (e * (σ * e * σ⁻¹)) * σ⁻¹ = e * (σ * e * σ⁻¹) := by
    have h1 : σ * (σ * e * σ⁻¹) * σ⁻¹ = (σ * σ) * e * (σ * σ)⁻¹ := by group
    have h2 : (σ * σ) * e * (σ * σ)⁻¹ = e := by
      have := hWc _ hσ2 _ heW
      calc (σ * σ) * e * (σ * σ)⁻¹ = (e * (σ * σ)) * (σ * σ)⁻¹ := by rw [this]
        _ = e := by group
    calc σ * (e * (σ * e * σ⁻¹)) * σ⁻¹ = (σ * e * σ⁻¹) * (σ * (σ * e * σ⁻¹) * σ⁻¹) := by group
      _ = (σ * e * σ⁻¹) * e := by rw [h1, h2]
      _ = e * (σ * e * σ⁻¹) := hWc _ heσW _ heW
  have ha₀tz : e * (σ * e * σ⁻¹) = t ∨ e * (σ * e * σ⁻¹) = z * t := by
    rcases d.late_inv_W _ ha₀W ha₀2 with h | h | h | h
    · exact absurd h ha₀1
    · exact absurd h ha₀z
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨ha₀tz, ?_⟩
  rcases d.late_S_act_t hσ with h | h
  · exact h
  · exfalso
    have hne : z * t ≠ t := fun h' => hz1 (by simpa using h')
    rcases ha₀tz with ha | ha
    · rw [ha, h] at hfix
      exact hne hfix
    · rw [ha] at hfix
      have : σ * (z * t) * σ⁻¹ = z * (z * t) := by
        calc σ * (z * t) * σ⁻¹ = (σ * z * σ⁻¹) * (σ * t * σ⁻¹) := by group
          _ = z * (z * t) := by rw [hσz, h]
      rw [this] at hfix
      apply hne
      calc z * t = z * (z * t) := hfix.symm
        _ = t := by rw [← mul_assoc, d.viol.hzK.sq, one_mul]

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
