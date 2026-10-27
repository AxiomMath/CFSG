module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10Gen

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzR10 Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {x₁ x₂ lam rho tau : G} {T₂ : Subgroup G}
variable (D : FzRNum t x₁ x₂ lam rho tau T₂)

theorem fzr_th_t : fzrTh D (fzrPar D).tI := by
  obtain ⟨htI, -⟩ := fzrPar_nums D
  refine ⟨?_, 1, ?_⟩
  · rw [htI]; norm_num
  · rw [htI, one_mul, inv_one, mul_one]
    exact (fzrMu_tI D).symm

theorem fzr_th_inv (ht2 : t * t = 1) (ht1 : t ≠ 1) {x : ℕ} (h : fzrTh D x) :
    x < 512 ∧ x ≠ 0 ∧ (fzrPar D).e x x = 0 := by
  obtain ⟨hx, g, hg⟩ := h
  have hsq : fzrMu D x * fzrMu D x = 1 := by
    rw [← hg]
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [ht2]
      _ = 1 := by group
  have he : (fzrPar D).e x x = 0 := by
    apply fzrMu_inj D ((fzrPar_mul D).lt x x hx hx) (by norm_num)
    rw [fzrMu_mul D hx hx, hsq, fzrMu_zero]
  refine ⟨hx, ?_, he⟩
  intro hx0
  apply ht1
  have hgt : g * t * g⁻¹ = 1 := by rw [hg, hx0, fzrMu_zero]
  calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
    _ = g⁻¹ * 1 * g := by rw [hgt]
    _ = 1 := by group

private theorem fzrAux_th_conj_key {g x y : ℕ} (hg : g < 512) (hx : x < 512) (hy : y < 512)
    (h : (fzrPar D).e y g = (fzrPar D).e g x) :
    fzrMu D y = fzrMu D g * fzrMu D x * (fzrMu D g)⁻¹ := by
  have h1 := congrArg (fzrMu D) h
  rw [fzrMu_mul D hy hg, fzrMu_mul D hg hx] at h1
  calc fzrMu D y = fzrMu D y * fzrMu D g * (fzrMu D g)⁻¹ := by group
    _ = fzrMu D g * fzrMu D x * (fzrMu D g)⁻¹ := by rw [h1]

theorem fzr_th_conj {g x y : ℕ} (hg : g < 512) (hx : x < 512) (hy : y < 512)
    (h : (fzrPar D).e y g = (fzrPar D).e g x) : fzrTh D x ↔ fzrTh D y := by
  have hkey := fzrAux_th_conj_key D hg hx hy h
  constructor
  · rintro ⟨-, b, hb⟩
    exact ⟨hy, fzrMu D g * b, by
      calc fzrMu D g * b * t * (fzrMu D g * b)⁻¹
          = fzrMu D g * (b * t * b⁻¹) * (fzrMu D g)⁻¹ := by group
        _ = fzrMu D g * fzrMu D x * (fzrMu D g)⁻¹ := by rw [hb]
        _ = fzrMu D y := hkey.symm⟩
  · rintro ⟨-, b, hb⟩
    exact ⟨hx, (fzrMu D g)⁻¹ * b, by
      calc (fzrMu D g)⁻¹ * b * t * ((fzrMu D g)⁻¹ * b)⁻¹
          = (fzrMu D g)⁻¹ * (b * t * b⁻¹) * fzrMu D g := by group
        _ = (fzrMu D g)⁻¹ * fzrMu D y * fzrMu D g := by rw [hb]
        _ = fzrMu D x := by rw [hkey]; group⟩

theorem fzr_th_rho {x : ℕ} (hx : x < 256) :
    fzrTh D x ↔ fzrTh D ((fzrPar D).rhoMap x) := by
  have hrho := fzrMu_rho D hx
  have hlt : (fzrPar D).rhoMap x < 512 := (fzrPar_lt D).2.2.2 x hx
  constructor
  · rintro ⟨-, b, hb⟩
    exact ⟨hlt, rho * b, by
      calc rho * b * t * (rho * b)⁻¹ = rho * (b * t * b⁻¹) * rho⁻¹ := by group
        _ = rho * fzrMu D x * rho⁻¹ := by rw [hb]
        _ = fzrMu D ((fzrPar D).rhoMap x) := hrho.symm⟩
  · rintro ⟨-, b, hb⟩
    exact ⟨by omega, rho⁻¹ * b, by
      calc rho⁻¹ * b * t * (rho⁻¹ * b)⁻¹
          = rho⁻¹ * (b * t * b⁻¹) * rho := by group
        _ = rho⁻¹ * fzrMu D ((fzrPar D).rhoMap x) * rho := by rw [hb]
        _ = fzrMu D x := by rw [hrho]; group⟩

end CFSG.OddStandard.SmallF3.FritzII
