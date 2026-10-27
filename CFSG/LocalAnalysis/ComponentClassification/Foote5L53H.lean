module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53E
public import CFSG.LocalAnalysis.ComponentClassification.Foote5TypesC

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

theorem R_le_centralizer {w : G} (hwQ : w ∈ Q) :
    S ⊓ L ≤ S ⊓ centralizer ({w} : Set G) := fun _ hr =>
  mem_inf.mpr ⟨(mem_inf.mp hr).1, mem_centralizer_singleton_iff.mpr (h.commute_Q_R hwQ hr).symm⟩

theorem conj_z_mem_center {w b : G} (hwQ : w ∈ Q)
    (hb : b ∈ normalizer ((S ⊓ centralizer ({w} : Set G) : Subgroup G) : Set G)) :
    b⁻¹ * z * b ∈ S ⊓ centralizer ({w} : Set G) ∧
      ∀ s ∈ S ⊓ centralizer ({w} : Set G), s * (b⁻¹ * z * b) = b⁻¹ * z * b * s := by
  have hcwz : w * z = z * w := h.zS w (h.QS hwQ)
  have hzS₀ : z ∈ S ⊓ centralizer ({w} : Set G) :=
    mem_inf.mpr ⟨h.zS_mem, mem_centralizer_singleton_iff.mpr hcwz.symm⟩
  refine ⟨conj_mem_of_mem_normalizer hb hzS₀, fun s hs => ?_⟩
  have h1 : b * s * b⁻¹ ∈ S ⊓ centralizer ({w} : Set G) := (mem_normalizer_iff.mp hb s).mp hs
  have h2 := h.zS _ (mem_inf.mp h1).1
  calc s * (b⁻¹ * z * b) = b⁻¹ * ((b * s * b⁻¹) * z) * b := by group
    _ = b⁻¹ * (z * (b * s * b⁻¹)) * b := by rw [h2]
    _ = b⁻¹ * z * b * s := by group

theorem zb_not_mem_lin (hD : Foote5AutData 𝕊 Lin)
    (hz51 : ∀ y, (∀ s ∈ S, s * y = y * s) → IsConj z y → y ∈ Q) {w b n : G}
    (hwQ : w ∈ Q) (hw2 : orderOf w = 2) (hwz : w ≠ z)
    (hnw : ∀ y, (∀ s ∈ S, s * y = y * s) → ¬ IsConj w y) (hn : n * w * n⁻¹ = w * z)
    (hb : b ∈ normalizer ((S ⊓ centralizer ({w} : Set G) : Subgroup G) : Set G))
    (hbw : b⁻¹ * w * b = w * t) : actG L ε (b⁻¹ * z * b) ∉ Lin := by
  have hw22 : w * w = 1 := by rw [← sq, ← hw2, pow_orderOf_eq_one]
  have hz22 : z * z = 1 := by rw [← sq, ← h.z2, pow_orderOf_eq_one]
  have ht22 : t * t = 1 := by rw [← sq, ← h.t2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := fun h1 => by have := h.z2; rw [h1, orderOf_one] at this; omega
  have hcwz : w * z = z * w := h.zS w (h.QS hwQ)
  obtain ⟨ζ, hζ⟩ : ∃ ζ, b⁻¹ * z * b = ζ := ⟨_, rfl⟩
  obtain ⟨hζS₀, hζc⟩ := h.conj_z_mem_center hwQ hb
  rw [hζ] at hζS₀ hζc ⊢
  have hζS : ζ ∈ S := (mem_inf.mp hζS₀).1
  have hζw : ζ * w = w * ζ := mem_centralizer_singleton_iff.mp (mem_inf.mp hζS₀).2
  have hζζ : ζ * ζ = 1 := by
    rw [← hζ, show b⁻¹ * z * b * (b⁻¹ * z * b) = b⁻¹ * (z * z) * b by group, hz22]; group
  have hζR : ∀ r ∈ S ⊓ L, ζ * r = r * ζ := fun r hr => (hζc r (h.R_le_centralizer hwQ hr)).symm
  have hζN := h.S_le hζS
  intro hlin
  by_cases hinn : actG L ε ζ ∉ innAut5 𝕊
  ·
    have hsq : actG L ε ζ * actG L ε ζ = 1 := by rw [← actG_mul ε hζN hζN, hζζ, actG_one]
    have hfix2 := hD.pgl_fixed (h.Rbar ε) _ hlin hinn hsq (h.actG_map_Rbar ε hζS)
    have hle : (h.Rbar ε : Subgroup 𝕊) ≤ (h.Rbar ε : Subgroup 𝕊) ⊓
        MonoidHom.eqLocus (actG L ε ζ).toMonoidHom (MonoidHom.id 𝕊) :=
      le_inf le_rfl fun ρ' hρ' => (h.actG_fix_iff ε hζS).mpr hζR ρ' hρ'
    have h3 := card_le_of_le hle
    rw [h.card_Rbar ε] at h3
    have h4 := h.four_le_card_R
    omega
  push Not at hinn
  obtain ⟨q, ρ, hqW, hρ, hρρ, hζe, hk⟩ := h.exists_conj_qt ε hwQ hw2 hwz hζS hζw hζζ hinn
  have hzζ : IsConj z ζ := isConj_iff.mpr ⟨b⁻¹, by rw [inv_inv, hζ]⟩
  have hwzw : IsConj w (w * z) := isConj_iff.mpr ⟨n, hn⟩
  have hzt_not : ¬ IsConj z t := fun h2 => h.t_not_mem_Q (hz51 t h.tZ h2)
  have hzzt_not : ¬ IsConj z (z * t) := fun h2 => h.t_not_mem_Q (by
    rw [show t = z⁻¹ * (z * t) by group]; exact mul_mem (inv_mem h.zQ) (hz51 _ h.zt_center h2))
  have hwzb : IsConj (w * z) (w * t * ζ) := isConj_iff.mpr ⟨b⁻¹, by
    rw [inv_inv, ← hbw, ← hζ]; group⟩
  by_cases hρ1 : ρ = 1
  · rw [hρ1, mul_one] at hζe
    rcases hqW with hq | hq | hq | hq <;> rw [hq] at hζe
    · apply hz1
      calc z = b * (b⁻¹ * z * b) * b⁻¹ := by group
        _ = 1 := by rw [hζ, hζe]; group
    · rw [hζe] at hzζ
      exact hnw z h.zS hzζ.symm
    ·
      have hbz : b ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.mpr (by
        calc b * z = b * (b⁻¹ * z * b) := by rw [hζ, hζe]
          _ = z * b := by group)
      have hwtC : w * t ∈ coreActionKernel L := by
        rw [← hbw]
        exact conj_mem_of_mem_normalizer (normalizer_le_normalizer_coreActionKernel L
          (h.centralizer_le_normalizer hbz)) (h.Q_le hwQ)
      have hwtQ : w * t ∈ Q := by
        rw [← h.inf_coreActionKernel]
        exact mem_inf.mpr ⟨mul_mem (h.QS hwQ) h.tS, hwtC⟩
      exact h.t_not_mem_Q (by
        rw [show t = w⁻¹ * (w * t) by group]; exact mul_mem (inv_mem hwQ) hwtQ)
    · rw [hζe] at hzζ
      exact hnw z h.zS (hwzw.trans hzζ.symm)
  obtain ⟨k, -, -, hk'⟩ := hk hρ1
  have hzqt : IsConj z (q * t) := hzζ.trans (isConj_iff.mpr ⟨k⁻¹, by rw [inv_inv, hk']⟩)
  have htρR : t * ρ ∈ S ⊓ L := mul_mem h.tR hρ
  have htρ2 : ρ ≠ t → orderOf (t * ρ) = 2 := fun hρt => by
    refine orderOf_eq_prime ?_ fun h2 => hρt ?_
    · rw [sq, show t * ρ * (t * ρ) = t * (ρ * t) * ρ by group, h.tZ ρ (mem_inf.mp hρ).1,
        show t * (t * ρ) * ρ = (t * t) * (ρ * ρ) by group, ht22, hρρ, one_mul]
    · calc ρ = t * (t * ρ) := by rw [← mul_assoc, ht22, one_mul]
        _ = t := by rw [h2, mul_one]
  rcases hqW with hq | hq | hq | hq <;> rw [hq] at hzqt hζe
  · exact hzt_not (by rwa [one_mul] at hzqt)
  ·
    have hwz' : IsConj (w * z) (t * ρ) := by
      have h2 : w * t * ζ = t * ρ := by
        rw [hζe]
        calc w * t * (w * ρ) = t * w * (w * ρ) := by rw [h.tZ w (h.QS hwQ)]
          _ = t * (w * w) * ρ := by group
          _ = t * ρ := by rw [hw22, mul_one]
      rw [← h2]
      exact hwzb
    by_cases hρt : ρ = t
    · rw [hρt, ht22] at hwz'
      have h3 : w * z = 1 := isConj_one_left.mp hwz'
      apply hwz
      calc w = w * z * z := by rw [mul_assoc, hz22, mul_one]
        _ = z := by rw [h3, one_mul]
    · obtain ⟨k₂, -, hk₂⟩ := h.exists_conj_t htρR (htρ2 hρt)
      have h3 : IsConj (t * ρ) t := isConj_iff.mpr ⟨k₂⁻¹, by rw [inv_inv, hk₂]⟩
      exact hnw t h.tZ (hwzw.trans (hwz'.trans h3))
  · exact hzzt_not hzqt
  ·
    have hwz' : IsConj (w * z) (z * (t * ρ)) := by
      have h2 : w * t * ζ = z * (t * ρ) := by
        rw [hζe]
        calc w * t * (w * z * ρ) = t * w * (w * z * ρ) := by rw [h.tZ w (h.QS hwQ)]
          _ = t * (w * w) * z * ρ := by group
          _ = z * (t * ρ) := by rw [hw22, mul_one, ← h.tZ z h.zS_mem, mul_assoc]
      rw [← h2]
      exact hwzb
    by_cases hρt : ρ = t
    · rw [hρt, ht22, mul_one] at hwz'
      exact hnw z h.zS (hwzw.trans hwz')
    · obtain ⟨k₃, -, hk₃C, hk₃⟩ := h.exists_conj_t_footeF hwQ hw2
        (h.isPGroup_Q.to_le inf_le_left) inf_le_left (fun x hx => (mem_inf.mp hx).2) htρR
        (htρ2 hρt)
      have hk₃z : k₃⁻¹ * z * k₃ = z := by
        have h2 := mem_centralizer_iff.mp hk₃C z (mem_inf.mpr ⟨h.zQ,
          mem_centralizer_singleton_iff.mpr hcwz.symm⟩)
        rw [mul_assoc, h2]; group
      have h3 : IsConj (z * (t * ρ)) (z * t) := isConj_iff.mpr ⟨k₃⁻¹, by
        rw [inv_inv, show k₃⁻¹ * (z * (t * ρ)) * k₃ = k₃⁻¹ * z * k₃ * (k₃⁻¹ * (t * ρ) * k₃) by
          group, hk₃z, hk₃]⟩
      exact hnw _ h.zt_center (hwzw.trans (hwz'.trans h3))

include ε in
theorem nonabelian_R_of_zb (hD : Foote5AutData 𝕊 Lin) {w b : G} (hwQ : w ∈ Q)
    (hb : b ∈ normalizer ((S ⊓ centralizer ({w} : Set G) : Subgroup G) : Set G))
    (hlin : actG L ε (b⁻¹ * z * b) ∉ Lin) : ∃ a ∈ S ⊓ L, ∃ c ∈ S ⊓ L, a * c ≠ c * a := by
  have hz22 : z * z = 1 := by rw [← sq, ← h.z2, pow_orderOf_eq_one]
  obtain ⟨hζS₀, hζc⟩ := h.conj_z_mem_center hwQ hb
  have hζS := (mem_inf.mp hζS₀).1
  have hζN := h.S_le hζS
  have hsq : actG L ε (b⁻¹ * z * b) * actG L ε (b⁻¹ * z * b) = 1 := by
    rw [← actG_mul ε hζN hζN, show b⁻¹ * z * b * (b⁻¹ * z * b) = b⁻¹ * (z * z) * b by group,
      hz22, show b⁻¹ * 1 * b = 1 by group, actG_one]
  exact h.nonabelian_R_of_fix ε hD hlin hsq ((h.actG_fix_iff ε hζS).mpr fun r hr =>
    (hζc r (h.R_le_centralizer hwQ hr)).symm)

end Sec5

end CFSG.ComponentClassification.Foote5
