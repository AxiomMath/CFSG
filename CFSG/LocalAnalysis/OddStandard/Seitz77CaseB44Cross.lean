module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Basic

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.OddStandard.Seitz77.CaseB45

theorem cross_of_weyl {G : Type} [Group G] {t σa σb : G} {Yp Yq Yg A₁ B₁ : Subgroup G}
    (hσa : σa * t = t * σa) (hσb : σb * t = t * σb)
    (hε : ∀ y ∈ A₁, ((σb * σa * σb)⁻¹ * (σa * σb * σa)) * y =
      y * ((σb * σa * σb)⁻¹ * (σa * σb * σa)))
    (hYp : Yp ≤ A₁) (hYq : Yq ≤ A₁)
    (hpg : cs σa Yp = Yg) (hgp : cs σa Yg = Yp) (hqg : cs σb Yq = Yg) (hgq : cs σb Yg = Yq)
    (hAB : ∀ x ∈ A₁, ∀ y ∈ B₁, x * y = y * x) (hB : cs t A₁ = B₁) :
    ∀ x ∈ cs σa Yq, ∀ y ∈ cs t (cs σb Yp), x * y = y * x := by
  have hww : σa * σb * σa = (σb * σa * σb) * ((σb * σa * σb)⁻¹ * (σa * σb * σa)) := by
    group
  have h1 : cs (σb * σa * σb) Yq = cs σb Yp := by
    rw [cs_mul, cs_mul, hqg, hgp]
  have h2 : cs (σa * σb * σa) Yp = cs σa Yq := by
    rw [cs_mul, cs_mul, hpg, hgq]
  have h3 : cs ((σb * σa * σb)⁻¹ * (σa * σb * σa)) Yp = Yp := by
    generalize (σb * σa * σb)⁻¹ * (σa * σb * σa) = ε at hε ⊢
    apply le_antisymm
    · intro y hy
      rw [mem_cs] at hy
      have hz := hε _ (hYp hy)
      have e : ε * (ε⁻¹ * y * ε) = y * ε := by group
      rw [e] at hz
      have hy' : ε⁻¹ * y * ε = y := mul_right_cancel hz.symm
      rwa [hy'] at hy
    · intro y hy
      rw [mem_cs]
      have hz := hε y (hYp hy)
      have e : ε⁻¹ * y * ε = y := by
        rw [mul_assoc, ← hz, inv_mul_cancel_left]
      rwa [e]
  have h4 : cs σa Yq = cs (σb * σa * σb) Yp := by
    rw [← h2, hww, cs_mul, h3]
  have hwt : Commute (σb * σa * σb) t :=
    Commute.mul_left (Commute.mul_left (hσb : Commute σb t) (hσa : Commute σa t))
      (hσb : Commute σb t)
  have h5 : cs t (cs (σb * σa * σb) Yq) = cs (σb * σa * σb) (cs t Yq) := by
    rw [← cs_mul, ← cs_mul, hwt.eq]
  have h6 : cs t Yq ≤ B₁ := by
    rw [← hB]
    exact cs_mono t hYq
  intro x hx y hy
  rw [h4] at hx
  rw [← h1, h5] at hy
  generalize σb * σa * σb = w at hx hy
  have hx₀ : w⁻¹ * x * w ∈ Yp := mem_cs.1 hx
  have hy₀ : w⁻¹ * y * w ∈ B₁ := h6 (mem_cs.1 hy)
  have hc := hAB _ (hYp hx₀) _ hy₀
  have e1 : w⁻¹ * x * w * (w⁻¹ * y * w) = w⁻¹ * (x * y) * w := by group
  have e2 : w⁻¹ * y * w * (w⁻¹ * x * w) = w⁻¹ * (y * x) * w := by group
  rw [e1, e2] at hc
  exact mul_left_cancel (mul_right_cancel hc)

end CFSG.OddStandard.Seitz77
