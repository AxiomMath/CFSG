module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseBasic

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

omit [Finite G] in
theorem mem_fusionSet_mul_of_section {R : Subgroup G} {e₀ b : G} (he₀ : e₀ ∈ FusionSet L z)
    (hb : b ∈ L) (hb2 : orderOf b = 2) (he₀R : e₀ ∈ R) (hbC : b ∈ centralizer (R : Set G))
    (hne : b * e₀ ≠ 1) (hsec : ∃ h' ∈ centralizer (R : Set G), h' * z * h'⁻¹ = z * b) :
    b * e₀ ∈ FusionSet L z := by
  obtain ⟨he₀L, he₀2, g, hg⟩ := he₀
  obtain ⟨h', hh', hzb⟩ := hsec
  have hcomm : e₀ * b = b * e₀ := mem_centralizer_iff.1 hbC e₀ he₀R
  have hh'e : h' * e₀ = e₀ * h' := by
    have := mem_centralizer_iff.1 hh' e₀ he₀R
    exact this.symm
  refine ⟨mul_mem hb he₀L, ?_, h' * g, ?_⟩
  · have hsq : (b * e₀) ^ 2 = 1 := by
      have hb1 : b * b = 1 := by rw [← sq]; exact hb2 ▸ pow_orderOf_eq_one b
      have he1 : e₀ * e₀ = 1 := by rw [← sq]; exact he₀2 ▸ pow_orderOf_eq_one e₀
      calc (b * e₀) ^ 2 = b * (e₀ * b) * e₀ := by rw [pow_two]; simp only [mul_assoc]
        _ = b * (b * e₀) * e₀ := by rw [hcomm]
        _ = (b * b) * (e₀ * e₀) := by group
        _ = 1 := by rw [hb1, he1, one_mul]
    exact orderOf_eq_prime hsq hne
  · calc h' * g * z * (h' * g)⁻¹ = h' * (g * z * g⁻¹) * h'⁻¹ := by group
      _ = h' * (z * e₀) * h'⁻¹ := by rw [hg]
      _ = (h' * z * h'⁻¹) * (h' * e₀ * h'⁻¹) := by group
      _ = (z * b) * e₀ := by
          rw [hzb, hh'e]; group
      _ = z * (b * e₀) := by group

theorem fusionAll_of_section_fusion (h : Setting G L n) (d : Cyc L Q z) {R : Subgroup G}
    {e₀ : G} (he₀R : e₀ ∈ R) (he₀2 : orderOf e₀ = 2) (he₀L : e₀ ∈ L)
    (hsec : ∀ b ∈ L, b ∈ centralizer (R : Set G) → orderOf b = 2 →
      ∃ h' ∈ centralizer (R : Set G), h' * z * h'⁻¹ = z * b)
    (hcov : ∀ y ∈ L, orderOf y = 2 → ∃ l ∈ L, (l * y * l⁻¹ ∈ centralizer (R : Set G) ∨
      ∃ b ∈ L, b ∈ centralizer (R : Set G) ∧ orderOf b = 2 ∧ b * e₀ ≠ 1 ∧ l * y * l⁻¹ = b * e₀))
    (he₀cov : ∃ l ∈ L, l * e₀ * l⁻¹ ∈ centralizer (R : Set G)) : FusionAll L z := by
  have hY : ∀ b ∈ L, b ∈ centralizer (R : Set G) → orderOf b = 2 → b ∈ FusionSet L z := by
    intro b hb hbC hb2
    obtain ⟨h', -, hh'⟩ := hsec b hb hbC hb2
    exact ⟨hb, hb2, h', hh'⟩
  have he₀Y : e₀ ∈ FusionSet L z := by
    obtain ⟨l, hl, hlC⟩ := he₀cov
    have hl2 : orderOf (l * e₀ * l⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact he₀2
    have := hY _ (mul_mem (mul_mem hl he₀L) (inv_mem hl)) hlC hl2
    have h2 := FusionSet.conj h d this (inv_mem hl)
    simpa [mul_assoc] using h2
  rw [fusionAll_iff]
  intro y hy hy2
  obtain ⟨l, hl, hcase⟩ := hcov y hy hy2
  have hlinv : ∀ w ∈ FusionSet L z, l * y * l⁻¹ = w → y ∈ FusionSet L z := by
    intro w hw hwy
    have := FusionSet.conj h d hw (inv_mem hl)
    rw [← hwy] at this
    simpa [mul_assoc] using this
  rcases hcase with hC | ⟨b, hb, hbC, hb2, hne, hby⟩
  · refine hlinv (l * y * l⁻¹) (hY _ (mul_mem (mul_mem hl hy) (inv_mem hl)) hC ?_) rfl
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact hy2
  · exact hlinv (b * e₀) (mem_fusionSet_mul_of_section he₀Y hb hb2 he₀R hbC hne
      (hsec b hb hbC hb2)) hby

end CFSG.OddStandard.AltStdSec
