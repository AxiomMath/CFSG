module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L51C
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53B
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L51B

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

omit [Finite 𝕊] in
theorem exists_conj_qt {w y : G} (hwQ : w ∈ Q) (hw2 : orderOf w = 2) (hwz : w ≠ z)
    (hyS : y ∈ S) (hyw : y * w = w * y) (hy2 : y * y = 1) (hinn : actG L ε y ∈ innAut5 𝕊) :
    ∃ q ρ : G, (q = 1 ∨ q = w ∨ q = z ∨ q = w * z) ∧ ρ ∈ S ⊓ L ∧ ρ * ρ = 1 ∧ y = q * ρ ∧
      (ρ ≠ 1 → ∃ k ∈ footeF L₀ w, k ∈ centralizer ((Q ⊓ centralizer ({w} : Set G) :
        Subgroup G) : Set G) ∧ k⁻¹ * y * k = q * t) := by
  have hw22 : w * w = 1 := by rw [← sq, ← hw2, pow_orderOf_eq_one]
  have hw1 : w ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hw2; omega
  obtain ⟨q, hq, ρ, hρ, rfl⟩ := h.exists_mul_of_inner ε hyS hinn
  have hqρ := h.commute_Q_R hq hρ
  have hqq : q * q = 1 := by
    have h1 : q * q * (ρ * ρ) = 1 := by
      rw [← hy2, show q * ρ * (q * ρ) = q * (ρ * q) * ρ by group, ← hqρ]
      group
    have h2 : q * q ∈ Q ⊓ L := by
      refine mem_inf.mpr ⟨mul_mem hq hq, ?_⟩
      rw [eq_inv_of_mul_eq_one_left h1]
      exact inv_mem (mul_mem (mem_inf.mp hρ).2 (mem_inf.mp hρ).2)
    rw [h.Q_inf_L, mem_bot] at h2
    exact h2
  have hρρ : ρ * ρ = 1 := by
    rw [← hy2, show q * ρ * (q * ρ) = q * (ρ * q) * ρ by group, ← hqρ,
      show q * (q * ρ) * ρ = q * q * (ρ * ρ) by group, hqq, one_mul]
  have hρw : ρ * w = w * ρ := (h.commute_Q_R hwQ hρ).symm
  have hqw : q * w = w * q := by
    have h1 : q * (ρ * w) = q * (w * ρ) := by rw [hρw]
    have h2 : q * ρ * w = w * (q * ρ) := hyw
    calc q * w = q * w * ρ * ρ⁻¹ := by group
      _ = q * (w * ρ) * ρ⁻¹ := by group
      _ = q * (ρ * w) * ρ⁻¹ := by rw [hρw]
      _ = w * (q * ρ) * ρ⁻¹ := by rw [← mul_assoc, h2]
      _ = w * q := by group
  have hqW := h.mem_W hwQ hw22 hw1 hwz hq hqq hqw
  refine ⟨q, ρ, hqW, hρ, hρρ, rfl, fun hρ1 => ?_⟩
  have hρ2 : orderOf ρ = 2 := orderOf_eq_prime (by rw [sq]; exact hρρ) hρ1
  have hW2 : IsPGroup 2 ↥(Q ⊓ centralizer ({w} : Set G)) := h.isPGroup_Q.to_le inf_le_left
  obtain ⟨k, hkF, hkC, hk⟩ := h.exists_conj_t_footeF hwQ hw2 hW2 inf_le_left
    (fun x hx => mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2)) hρ hρ2
  have hqC : q * k = k * q := mem_centralizer_iff.mp hkC q
    (mem_inf.mpr ⟨hq, mem_centralizer_singleton_iff.mpr hqw⟩)
  refine ⟨k, hkF, hkC, ?_⟩
  calc k⁻¹ * (q * ρ) * k = k⁻¹ * q * k * (k⁻¹ * ρ * k) := by group
    _ = q * t := by rw [show k⁻¹ * q * k = q by rw [mul_assoc, hqC]; group, hk]

theorem zt_center : ∀ s ∈ S, s * (z * t) = z * t * s := fun s hs => by
  rw [← mul_assoc, h.zS s hs, mul_assoc, h.tZ s hs, mul_assoc]

theorem t_not_mem_Q : t ∉ Q := fun htQ => by
  have h1 : t ∈ Q ⊓ L := mem_inf.mpr ⟨htQ, h.tL⟩
  rw [h.Q_inf_L, mem_bot] at h1
  exact h.t_ne_one h1

omit [Finite 𝕊] in
theorem za_inner_data (hz51 : ∀ y, (∀ s ∈ S, s * y = y * s) → IsConj z y → y ∈ Q) {w a n : G}
    (hwQ : w ∈ Q) (hw2 : orderOf w = 2) (hwz : w ≠ z) (hnS : n ∈ S)
    (hn : n * w * n⁻¹ = w * z) (hza : a⁻¹ * z * a ∈ S ⊓ centralizer ({w} : Set G))
    (hzaQ : a⁻¹ * z * a ∉ Q) (hinn : actG L ε (a⁻¹ * z * a) ∈ innAut5 𝕊) :
    ∃ q ρ : G, (q = w ∨ q = w * z) ∧ ρ ∈ S ⊓ L ∧ ρ * ρ = 1 ∧ a⁻¹ * z * a = q * ρ ∧
      IsConj z (w * t) ∧ IsConj z (w * z * t) := by
  have hz22 : z * z = 1 := by rw [← sq, ← h.z2, pow_orderOf_eq_one]
  have hA2 : a⁻¹ * z * a * (a⁻¹ * z * a) = 1 := by
    rw [show a⁻¹ * z * a * (a⁻¹ * z * a) = a⁻¹ * (z * z) * a by group, hz22]; group
  obtain ⟨q, ρ, hqW, hρ, hρρ, hA, hk⟩ := h.exists_conj_qt ε hwQ hw2 hwz (mem_inf.mp hza).1
    (mem_centralizer_singleton_iff.mp (mem_inf.mp hza).2) hA2 hinn
  have hqQ : q ∈ Q := by
    rcases hqW with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hwQ
    · exact h.zQ
    · exact mul_mem hwQ h.zQ
  have hρ1 : ρ ≠ 1 := fun h1 => hzaQ (by rw [hA, h1, mul_one]; exact hqQ)
  obtain ⟨k, -, -, hk'⟩ := hk hρ1
  have hzqt : IsConj z (q * t) :=
    (isConj_iff.mpr ⟨a⁻¹, by rw [inv_inv]⟩).trans (isConj_iff.mpr ⟨k⁻¹, by rw [inv_inv, hk']⟩)
  have hwt : IsConj (w * t) (w * z * t) := isConj_iff.mpr ⟨n, by
    rw [show n * (w * t) * n⁻¹ = n * w * n⁻¹ * (n * t * n⁻¹) by group, hn,
      h.tZ n hnS, mul_inv_cancel_right]⟩
  rcases hqW with hq | hq | hq | hq
  · rw [hq, one_mul] at hzqt
    exact absurd (hz51 t h.tZ hzqt) h.t_not_mem_Q
  · rw [hq] at hzqt hA
    exact ⟨w, ρ, Or.inl rfl, hρ, hρρ, hA, hzqt, hzqt.trans hwt⟩
  · exfalso
    rw [hq] at hzqt
    have h1 := hz51 _ h.zt_center hzqt
    exact h.t_not_mem_Q (by rw [show t = z⁻¹ * (z * t) by group]; exact mul_mem (inv_mem h.zQ) h1)
  · rw [hq] at hzqt hA
    exact ⟨w * z, ρ, Or.inr rfl, hρ, hρρ, hA, hzqt.trans hwt.symm, hzqt⟩

omit [Finite 𝕊] in
theorem wa_not_inner {w A₁ : G} (hwQ : w ∈ Q) (hw2 : orderOf w = 2) (hwz : w ≠ z)
    (hnw : ∀ y, (∀ s ∈ S, s * y = y * s) → ¬ IsConj w y) (hzwt : IsConj z (w * t))
    (hzwzt : IsConj z (w * z * t)) (h1 : A₁ ∈ S ⊓ centralizer ({w} : Set G)) (h1Q : A₁ ∉ Q)
    (h1c : IsConj w A₁) (h11 : A₁ * A₁ = 1) : actG L ε A₁ ∉ innAut5 𝕊 := by
  intro hinn
  obtain ⟨q, ρ, hqW, -, -, hA, hk⟩ := h.exists_conj_qt ε hwQ hw2 hwz (mem_inf.mp h1).1
    (mem_centralizer_singleton_iff.mp (mem_inf.mp h1).2) h11 hinn
  have hqQ : q ∈ Q := by
    rcases hqW with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hwQ
    · exact h.zQ
    · exact mul_mem hwQ h.zQ
  have hρ1 : ρ ≠ 1 := fun h2 => h1Q (by rw [hA, h2, mul_one]; exact hqQ)
  obtain ⟨k, -, -, hk'⟩ := hk hρ1
  have hwqt : IsConj w (q * t) := h1c.trans (isConj_iff.mpr ⟨k⁻¹, by rw [inv_inv, hk']⟩)
  rcases hqW with hq | hq | hq | hq <;> rw [hq] at hwqt
  · exact hnw t h.tZ (by rwa [one_mul] at hwqt)
  · exact hnw z h.zS (hwqt.trans hzwt.symm)
  · exact hnw _ h.zt_center hwqt
  · exact hnw z h.zS (hwqt.trans hzwzt.symm)

end Sec5

end CFSG.ComponentClassification.Foote5
