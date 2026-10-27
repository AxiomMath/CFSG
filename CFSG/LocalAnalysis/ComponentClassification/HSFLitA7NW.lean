module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NVW

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {T₁ : Subgroup X}

namespace Inst

variable (I : S.Inst)

theorem exists_w (H : S.Sec6Hyp T₁) : ∃ w ∈ T₁, w * S.t * w⁻¹ = S.t * S.z ∧
    w * S.z * w⁻¹ = S.z ∧ w * I.ki * w⁻¹ = I.ki ∧
      ((I.CaseI ∧ w * I.yi * w⁻¹ = I.yi) ∨ (¬ I.CaseI ∧ w * I.yi * w⁻¹ = I.yi * I.ki)) := by
  have htz : S.t * S.z = I.wV (1, 0, 1, 0) := by
    simp [wV, S.z_comm_of_mem_T S.data.t_mem_T]
  have htzB : S.t * S.z ∈ S.B := mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  have htzc : ConjTo S.t (S.t * S.z) := by rw [htz, I.conjTo_wV_iff H.fus]
  obtain ⟨w₀, hw₀, hw₀t⟩ := H.exists_conj_T₁ htzB htzc
  rw [htz] at hw₀t
  obtain ⟨p, q, a, hc⟩ := I.exists_tCols H hw₀ hw₀t
  obtain ⟨hz0, hy0, -, hk0⟩ := I.conj_of_cols hc
  have hz : w₀ * S.z * w₀⁻¹ = I.wV (1, 0, 0, 0) := hz0
  have hy : w₀ * I.yi * w₀⁻¹ = I.wV (p, 1, 0, q) := hy0
  have hk : w₀ * I.ki * w₀⁻¹ = I.wV (a, 0, 0, 1) := hk0
  clear hz0 hy0 hk0
  have hw₀N := I.T₁_le H hw₀
  have ha : a = 0 := by
    have h1 := I.k_fixed H hw₀N
    rw [hk, show I.ki = I.wV (0, 0, 0, 1) by simp [wV]] at h1
    have := I.wV_injective h1
    simp only [Prod.mk.injEq] at this
    exact this.1
  subst ha
  have hz' : w₀ * S.z * w₀⁻¹ = S.z := by simpa [wV] using hz
  have hk' : w₀ * I.ki * w₀⁻¹ = I.ki := by simpa [wV] using hk
  have ht' : w₀ * S.t * w₀⁻¹ = S.t * S.z := by rw [hw₀t, htz]
  have hxT := S.x_mem.1
  have hxB : ∀ {g : X}, g ∈ S.B → S.x * g * S.x⁻¹ = g := fun hg => by
    rw [← S.central_of_mem_B hg hxT]; group
  have hxt : S.x * S.t * S.x⁻¹ = S.t := hxB (subset_closure (by simp))
  have hxz : S.x * S.z * S.x⁻¹ = S.z := hxB (subset_closure (by simp))
  have hxk : S.x * I.ki * S.x⁻¹ = I.ki := hxB I.ki_mem_B
  obtain ⟨w, hwT, hwt, hwz, hwk, hwy⟩ : ∃ w ∈ T₁, w * S.t * w⁻¹ = S.t * S.z ∧
      w * S.z * w⁻¹ = S.z ∧ w * I.ki * w⁻¹ = I.ki ∧ w * I.yi * w⁻¹ = I.wV (0, 1, 0, q) := by
    rcases Fin.exists_fin_two.mp ⟨p, rfl⟩ with rfl | rfl
    · exact ⟨w₀, hw₀, ht', hz', hk', hy⟩
    · refine ⟨w₀ * S.x, mul_mem hw₀ (H.le hxT), ?_, ?_, ?_, ?_⟩
      · calc w₀ * S.x * S.t * (w₀ * S.x)⁻¹ = w₀ * (S.x * S.t * S.x⁻¹) * w₀⁻¹ := by group
          _ = S.t * S.z := by rw [hxt, ht']
      · calc w₀ * S.x * S.z * (w₀ * S.x)⁻¹ = w₀ * (S.x * S.z * S.x⁻¹) * w₀⁻¹ := by group
          _ = S.z := by rw [hxz, hz']
      · calc w₀ * S.x * I.ki * (w₀ * S.x)⁻¹ = w₀ * (S.x * I.ki * S.x⁻¹) * w₀⁻¹ := by group
          _ = I.ki := by rw [hxk, hk']
      · calc w₀ * S.x * I.yi * (w₀ * S.x)⁻¹ = w₀ * (S.x * I.yi * S.x⁻¹) * w₀⁻¹ := by group
          _ = (w₀ * S.z * w₀⁻¹) * (w₀ * I.yi * w₀⁻¹) := by rw [I.x_conj_yi]; group
          _ = I.wV (0, 1, 0, q) := by
              rw [hz', hy]
              have e : I.wV (1, 1, 0, q) = S.z * I.wV (0, 1, 0, q) := by
                rw [show ((1, 1, 0, q) : V4) = addV (1, 0, 0, 0) (0, 1, 0, q) by
                  simp [addV], I.wV_add]
                simp [wV]
              rw [e, ← mul_assoc, ← pow_two, S.z_sq, one_mul]
  have hwN := I.T₁_le H hwT
  refine ⟨w, hwT, hwt, hwz, hwk, ?_⟩
  rcases Fin.exists_fin_two.mp ⟨q, rfl⟩ with rfl | rfl
  · left
    have hwy' : w * I.yi * w⁻¹ = I.yi := by rw [hwy]; simp [wV]
    exact ⟨⟨w, hwN, hwt, hwz, hwy', hwk⟩, hwy'⟩
  · right
    have hwy' : w * I.yi * w⁻¹ = I.yi * I.ki := by rw [hwy]; simp [wV]
    refine ⟨fun ⟨g, hg, hgt, hgz, hgy, hgk⟩ => ?_, hwy'⟩
    have hm : g⁻¹ * w ∈ normalizer (I.E : Set X) ⊓ centralizer ({S.t} : Set X) := by
      refine mem_inf.mpr ⟨mul_mem (inv_mem hg) hwN, ?_⟩
      rw [mem_centralizer_singleton_iff]
      have hg' : g⁻¹ * (S.t * S.z) * g = S.t := by rw [← hgt]; group
      calc g⁻¹ * w * S.t = g⁻¹ * (w * S.t * w⁻¹) * g * (g⁻¹ * w) := by group
        _ = S.t * (g⁻¹ * w) := by rw [hwt, hg']
    have h3 := I.conj_mem_three H.fus hm (Or.inr (Or.inl rfl))
    have hgyi : g⁻¹ * I.yi * g = I.yi := by
      calc g⁻¹ * I.yi * g = g⁻¹ * (g * I.yi * g⁻¹) * g := by rw [hgy]
        _ = I.yi := by group
    have hgki : g⁻¹ * I.ki * g = I.ki := by
      calc g⁻¹ * I.ki * g = g⁻¹ * (g * I.ki * g⁻¹) * g := by rw [hgk]
        _ = I.ki := by group
    have e : g⁻¹ * w * I.yi * (g⁻¹ * w)⁻¹ = I.wV (0, 1, 0, 1) := by
      calc g⁻¹ * w * I.yi * (g⁻¹ * w)⁻¹ = g⁻¹ * (w * I.yi * w⁻¹) * g := by group
        _ = (g⁻¹ * I.yi * g) * (g⁻¹ * I.ki * g) := by rw [hwy']; group
        _ = I.wV (0, 1, 0, 1) := by rw [hgyi, hgki]; simp [wV]
    rw [e] at h3
    rcases h3 with h | h | h
    · have := I.wV_injective (h.trans (show S.z = I.wV (1, 0, 0, 0) by simp [wV]))
      simp at this
    · have := I.wV_injective (h.trans (show I.yi = I.wV (0, 1, 0, 0) by simp [wV]))
      simp at this
    · have := I.wV_injective (h.trans (show S.z * I.yi = I.wV (1, 1, 0, 0) by simp [wV]))
      simp at this

end Inst

end A7Base

end CFSG.ComponentClassification.HSFLit
