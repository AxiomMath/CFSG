module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB41Main

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup

section Gen

variable {G : Type} [Group G] {t : G}

theorem conj_conj_of_mul_self_eq_one (htt : t * t = 1) (x : G) : t * (t * x * t⁻¹) * t⁻¹ = x := by
  calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
    _ = x := by rw [htt]; group

end Gen

section Diag

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {t : G} {c : CaseB A R t}
  {M₁ M₂ : Subgroup G}

theorem CaseB.Factors.diag_mul (F : c.Factors M₁ M₂) (hZ : c.OddCoreCentral) {m n : G}
    (hm : m ∈ M₁) (hn : n ∈ M₁) :
    (m * n) * (t * (m * n) * t⁻¹) = (m * (t * m * t⁻¹)) * (n * (t * n * t⁻¹)) := by
  have h : n * (t * m * t⁻¹) = (t * m * t⁻¹) * n := F.comm_elem hZ hn (F.swap₁ m hm)
  calc (m * n) * (t * (m * n) * t⁻¹)
      = m * (n * (t * m * t⁻¹)) * (t * n * t⁻¹) := by group
    _ = m * ((t * m * t⁻¹) * n) * (t * n * t⁻¹) := by rw [h]
    _ = (m * (t * m * t⁻¹)) * (n * (t * n * t⁻¹)) := by group

theorem CaseB.Factors.diag_conj (F : c.Factors M₁ M₂) (hZ : c.OddCoreCentral) {m y : G}
    (hm : m ∈ M₁) (hy : y ∈ M₁) :
    (m * (t * m * t⁻¹)) * y * (m * (t * m * t⁻¹))⁻¹ = m * y * m⁻¹ := by
  have h : (t * m * t⁻¹) * y = y * (t * m * t⁻¹) := (F.comm_elem hZ hy (F.swap₁ m hm)).symm
  calc (m * (t * m * t⁻¹)) * y * (m * (t * m * t⁻¹))⁻¹
      = m * ((t * m * t⁻¹) * y) * (t * m * t⁻¹)⁻¹ * m⁻¹ := by group
    _ = m * (y * (t * m * t⁻¹)) * (t * m * t⁻¹)⁻¹ * m⁻¹ := by rw [h]
    _ = m * y * m⁻¹ := by group

theorem CaseB.Factors.exists_diag (F : c.Factors M₁ M₂) (hZ : c.OddCoreCentral) {σ : G}
    (hσ : σ ∈ c.Ninf) (hσt : σ * t = t * σ) : ∃ m ∈ M₁, σ = m * (t * m * t⁻¹) := by
  have hc : ∀ x ∈ M₁, ∀ y ∈ M₂, x * y = y * x := fun x hx y hy => F.comm_elem hZ hx hy
  have htt : t * t = 1 := c.t_mul_self
  have hσ' : t * σ * t⁻¹ = σ := by rw [← hσt]; group
  obtain ⟨a, ha, b, hb, hab⟩ :=
    mem_sup_of_forall_comm (O := M₁) (E := M₂) hc (F.ninf_eq ▸ hσ)
  have ha' : t * a * t⁻¹ ∈ M₂ := F.swap₁ a ha
  have hb' : t * b * t⁻¹ ∈ M₁ := F.swap₂ b hb
  have h1 : (t * b * t⁻¹) * (t * a * t⁻¹) = a * b := by
    calc (t * b * t⁻¹) * (t * a * t⁻¹) = (t * a * t⁻¹) * (t * b * t⁻¹) := hc _ hb' _ ha'
      _ = t * (a * b) * t⁻¹ := by group
      _ = a * b := by rw [← hab]; exact hσ'
  have h2 : a⁻¹ * (t * b * t⁻¹) = b * (t * a * t⁻¹)⁻¹ := by
    calc a⁻¹ * (t * b * t⁻¹) = a⁻¹ * ((t * b * t⁻¹) * (t * a * t⁻¹)) * (t * a * t⁻¹)⁻¹ := by
          group
      _ = a⁻¹ * (a * b) * (t * a * t⁻¹)⁻¹ := by rw [h1]
      _ = b * (t * a * t⁻¹)⁻¹ := by group
  obtain ⟨z₀, hz₀def⟩ : ∃ z₀, z₀ = a⁻¹ * (t * b * t⁻¹) := ⟨_, rfl⟩
  have hz₀ : z₀ ∈ M₁ ⊓ M₂ := by
    refine ⟨?_, ?_⟩
    · rw [hz₀def]; exact M₁.mul_mem (M₁.inv_mem ha) hb'
    · rw [hz₀def, h2]; exact M₂.mul_mem hb (M₂.inv_mem ha')
  obtain ⟨z, hzdef⟩ : ∃ z, z = t * z₀ * t⁻¹ := ⟨_, rfl⟩
  have hz : z ∈ M₁ ⊓ M₂ := by
    rw [hzdef]
    exact ⟨F.swap₂ z₀ hz₀.2, F.swap₁ z₀ hz₀.1⟩
  have hb_eq : b = (t * a * t⁻¹) * z := by
    calc b = t * (t * b * t⁻¹) * t⁻¹ := (conj_conj_of_mul_self_eq_one htt b).symm
      _ = t * (a * z₀) * t⁻¹ := by rw [hz₀def]; group
      _ = (t * a * t⁻¹) * z := by rw [hzdef]; group
  have hσ_eq : σ = a * (t * a * t⁻¹) * z := by
    calc σ = a * b := hab
      _ = a * ((t * a * t⁻¹) * z) := by rw [← hb_eq]
      _ = a * (t * a * t⁻¹) * z := by group
  have hzt : t * z * t⁻¹ = z := by
    have e1 : t * σ * t⁻¹ = (t * a * t⁻¹) * a * (t * z * t⁻¹) := by
      rw [hσ_eq]
      calc t * (a * (t * a * t⁻¹) * z) * t⁻¹
          = (t * a * t⁻¹) * (t * (t * a * t⁻¹) * t⁻¹) * (t * z * t⁻¹) := by group
        _ = (t * a * t⁻¹) * a * (t * z * t⁻¹) := by rw [conj_conj_of_mul_self_eq_one htt a]
    have e2 : (t * a * t⁻¹) * a = a * (t * a * t⁻¹) := (hc a ha _ ha').symm
    have e3 : (a * (t * a * t⁻¹)) * z = (a * (t * a * t⁻¹)) * (t * z * t⁻¹) := by
      calc (a * (t * a * t⁻¹)) * z = σ := hσ_eq.symm
        _ = t * σ * t⁻¹ := hσ'.symm
        _ = (t * a * t⁻¹) * a * (t * z * t⁻¹) := e1
        _ = (a * (t * a * t⁻¹)) * (t * z * t⁻¹) := by rw [e2]
    exact (mul_left_cancel e3).symm
  obtain ⟨k, hk⟩ := F.odd_inf
  have hzpow : z ^ (2 * k + 1) = 1 := by
    have := pow_card_eq_one' (G := ↥(M₁ ⊓ M₂)) (x := ⟨z, hz⟩)
    rw [hk] at this
    exact congrArg Subtype.val this
  obtain ⟨w, hwdef⟩ : ∃ w, w = z ^ (k + 1) := ⟨_, rfl⟩
  have hw : w ∈ M₁ ⊓ M₂ := by rw [hwdef]; exact pow_mem hz _
  have hww : w * w = z := by
    rw [hwdef, ← pow_add, show k + 1 + (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hzpow,
      one_mul]
  have hwt : t * w * t⁻¹ = w := by rw [hwdef, ← conj_pow, hzt]
  have ha'N : t * a * t⁻¹ ∈ c.Ninf := by rw [F.ninf_eq]; exact mem_sup_right ha'
  have hwc : w * (t * a * t⁻¹) = (t * a * t⁻¹) * w := F.inf_central hZ hw ha'N
  refine ⟨a * w, M₁.mul_mem ha hw.1, ?_⟩
  have e4 : t * (a * w) * t⁻¹ = (t * a * t⁻¹) * w := by
    calc t * (a * w) * t⁻¹ = (t * a * t⁻¹) * (t * w * t⁻¹) := by group
      _ = (t * a * t⁻¹) * w := by rw [hwt]
  rw [e4]
  calc σ = a * (t * a * t⁻¹) * z := hσ_eq
    _ = a * (t * a * t⁻¹) * (w * w) := by rw [hww]
    _ = a * ((t * a * t⁻¹) * w) * w := by group
    _ = a * (w * (t * a * t⁻¹)) * w := by rw [hwc]
    _ = (a * w) * ((t * a * t⁻¹) * w) := by group

end Diag

end CFSG.OddStandard.Seitz77
