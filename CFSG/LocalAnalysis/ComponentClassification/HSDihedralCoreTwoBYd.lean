module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTwoBYc

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup
open CFSG.ComponentClassification.HSFLit (ElemAbelianTwo)

variable {X : Type} [Group X] [Finite X] {A : Type} [Group A] [Finite A]

namespace LocalDatum

variable {Δ : LocalDatum X A} {k : A} (h2 : Δ.CaseTwo k) {φ : Δ.Fusion}

namespace TwoBY

variable (YD : TwoBY φ)

include h2 in
theorem false_of_Tbar {Tbar : Subgroup A} {m : ℕ} (e : ↥Tbar ≃* DihedralGroup m) (hm : Even m)
    (h8 : 8 ≤ m) (hTR : Tbar ≤ Δ.R) (hDT : Δ.Dbar ≤ Tbar) {y : X} (hy : y ∈ YD.Y)
    (hy1 : y ≠ 1) (hyt : y ≠ Δ.t) (hyz : y ≠ Δ.dz) (hytz : y ≠ Δ.t * Δ.dz)
    (hyT : Δ.ψe y ∈ Tbar) (hyD : Δ.ψe y ∉ Δ.Dbar) : False := by
  have hzT : Δ.ψe Δ.dz ∈ Tbar := hDT (Δ.ψe_mem_Dbar Δ.dz_mem)
  refine false_of_normal_elem h2 e hm h8 hTR hDT YD.le_S (fun s hs y' hy' => YD.conj_S hs hy')
    YD.elem (fun y' hy' => ?_) YD.dz_mem hy (fun h => hyD (h ▸ one_mem _))
    (fun h => hyD (h ▸ Δ.ψe_mem_Dbar Δ.dz_mem))
  rcases YD.ψe_cases hy hy1 hyt hyz hytz hy' with h | h | h | h <;> rw [h]
  · exact one_mem _
  · exact hzT
  · exact hyT
  · exact mul_mem hzT hyT

omit [Finite A] in
theorem inter_D {y : X} (hy : y ∈ YD.Y) (hy1 : y ≠ 1) (hyt : y ≠ Δ.t) (hyz : y ≠ Δ.dz)
    (hytz : y ≠ Δ.t * Δ.dz) (hyD : Δ.ψe y ∉ Δ.Dbar) :
    ∀ y' ∈ YD.Y, y' ∈ Δ.D → y' = 1 ∨ y' = Δ.dz := by
  have hyS := YD.le_S hy
  have hzinv : ∀ a : A, Δ.ψe Δ.dz * a ∈ Δ.Dbar → a ∈ Δ.Dbar := fun a ha => by
    have := mul_mem (inv_mem (Δ.ψe_mem_Dbar Δ.dz_mem)) ha
    rwa [inv_mul_cancel_left] at this
  have htD : ∀ a ∈ Δ.D, a ≠ Δ.t * Δ.dz := fun a ha h => Δ.t_not_mem_D (by
    have := mul_mem (h ▸ ha) (inv_mem Δ.dz_mem)
    rwa [mul_inv_cancel_right] at this)
  intro y' hy' hy'D
  have hψ := Δ.ψe_mem_Dbar hy'D
  rcases YD.cases hy hy1 hyt hyz hytz hy' with (h | h | h | h) | (rfl | rfl | rfl | rfl)
  · exact Or.inl h
  · exact absurd (h ▸ hy'D) Δ.t_not_mem_D
  · exact Or.inr h
  · exact absurd h (htD _ hy'D)
  · exact absurd hψ hyD
  · rw [Δ.ψe_mul Δ.t_mem hyS, Δ.ψe_t, one_mul] at hψ
    exact absurd hψ hyD
  · rw [Δ.ψe_mul (Δ.D_le Δ.dz_mem) hyS] at hψ
    exact absurd (hzinv _ hψ) hyD
  · rw [Δ.ψe_mul (mul_mem Δ.t_mem (Δ.D_le Δ.dz_mem)) hyS,
      Δ.ψe_mul Δ.t_mem (Δ.D_le Δ.dz_mem), Δ.ψe_t, one_mul] at hψ
    exact absurd (hzinv _ hψ) hyD

omit [Finite A] in
include h2 in
theorem field_decomp {y : X} (hy : y ∈ YD.Y) (hy1 : y ≠ 1) (hyt : y ≠ Δ.t) (hyz : y ≠ Δ.dz)
    (hytz : y ≠ Δ.t * Δ.dz) (hyk : Δ.ψe y * k ∈ Δ.Dbar) :
    ∃ d ∈ Δ.D, ∃ w₀ ∈ Δ.S, y = d * w₀ ∧ (∀ d' ∈ Δ.D, w₀ * d' = d' * w₀) ∧ Δ.ψe w₀ = k ∧
      d ^ 2 = 1 ∧ ∀ g ∈ Δ.D, d * g * d⁻¹ * g⁻¹ = 1 ∨ d * g * d⁻¹ * g⁻¹ = Δ.dz := by
  have hkinv : k⁻¹ = k := inv_eq_of_mul_eq_one_right (by rw [← pow_two, h2.2.2.2.1])
  have hyS := YD.le_S hy
  have hyD : Δ.ψe y ∉ Δ.Dbar := fun h => h2.2.2.1 (by
    have := mul_mem (inv_mem h) hyk
    rwa [inv_mul_cancel_left] at this)
  obtain ⟨w, hwS, hwk⟩ := (Δ.mem_R_iff).mp h2.1
  have hwD : ∀ d ∈ Δ.D, w * d = d * w := fun d hd =>
    (Δ.commute_iff hwS hd).mpr (by rw [hwk]; exact h2.2.1 _ (Δ.ψe_mem_Dbar hd))
  have hyw : Δ.ψe (y * w⁻¹) ∈ Δ.Dbar := by
    rw [Δ.ψe_mul hyS (inv_mem hwS), Δ.ψe_inv hwS, hwk, hkinv]
    exact hyk
  obtain ⟨q, hq, d, hd, hqd⟩ := Δ.exists_QD (mul_mem hyS (inv_mem hwS)) hyw
  have hqdc : q * d = d * q := Δ.commute_of_mem_Q_D hq hd
  have hyeq : y = d * (q * w) := by
    calc y = y * w⁻¹ * w := by group
      _ = d * (q * w) := by rw [hqd, hqdc, mul_assoc]
  have hw₀S : q * w ∈ Δ.S := mul_mem (Δ.Q_le hq) hwS
  have hw₀D : ∀ d' ∈ Δ.D, q * w * d' = d' * (q * w) := fun d' hd' => by
    rw [mul_assoc, hwD d' hd', ← mul_assoc, Δ.commute_of_mem_Q_D hq hd', mul_assoc]
  have hw₀k : Δ.ψe (q * w) = k := by
    rw [Δ.ψe_mul (Δ.Q_le hq) hwS, ((Δ.mem_Q_iff).mp hq).2, hwk, one_mul]
  have hYD := YD.inter_D hy hy1 hyt hyz hytz hyD
  refine ⟨d, hd, q * w, hw₀S, hyeq, hw₀D, hw₀k, ?_, fun g hg => ?_⟩
  · have hy2 := YD.elem.sq_eq_one y hy
    rw [hyeq, (show Commute d (q * w) from (hw₀D d hd).symm).mul_pow] at hy2
    have hqw2 : (q * w) ^ 2 ∈ Δ.Q := (Δ.mem_Q_iff).mpr ⟨pow_mem hw₀S 2, by
      rw [Δ.ψe_pow hw₀S, hw₀k, h2.2.2.2.1]⟩
    have : d ^ 2 ∈ Δ.Q := by
      rw [show d ^ 2 = ((q * w) ^ 2)⁻¹ by rw [← mul_eq_one_iff_eq_inv.mp hy2]]
      exact inv_mem hqw2
    exact Δ.eq_one_of_mem_Q_D this (pow_mem hd 2)
  · have hgw₀ : g * (q * w) = (q * w) * g := (hw₀D g hg).symm
    have h' : (q * w) * g⁻¹ = g⁻¹ * (q * w) := by
      calc (q * w) * g⁻¹ = g⁻¹ * (g * (q * w)) * g⁻¹ := by group
        _ = g⁻¹ * ((q * w) * g) * g⁻¹ := by rw [hgw₀]
        _ = g⁻¹ * (q * w) := by group
    have he : g * y * g⁻¹ * y⁻¹ = g * d * g⁻¹ * d⁻¹ := by
      rw [hyeq]
      calc g * (d * (q * w)) * g⁻¹ * (d * (q * w))⁻¹ =
          g * d * ((q * w) * g⁻¹) * (q * w)⁻¹ * d⁻¹ := by group
        _ = g * d * (g⁻¹ * (q * w)) * (q * w)⁻¹ * d⁻¹ := by rw [h']
        _ = g * d * g⁻¹ * d⁻¹ := by group
    have hmemY : g * d * g⁻¹ * d⁻¹ ∈ YD.Y := he ▸ mul_mem (YD.conj_S (Δ.D_le hg) hy) (inv_mem hy)
    have hmemD : g * d * g⁻¹ * d⁻¹ ∈ Δ.D := mul_mem (Δ.conj_mem_D g (Δ.D_le hg) d hd) (inv_mem hd)
    have hinv : d * g * d⁻¹ * g⁻¹ = (g * d * g⁻¹ * d⁻¹)⁻¹ := by group
    rcases hYD _ hmemY hmemD with h | h
    · left; rw [hinv, h, inv_one]
    · right; rw [hinv, h, inv_eq_of_mul_eq_one_right (by rw [← pow_two, Δ.dz_sq])]

end TwoBY

end LocalDatum

end CFSG.ComponentClassification.HSDihedral
