module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBV1

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {c : Bool} {t : G} {T₂ P : Subgroup G}
  {x₁ x₂ q s lam : G} {β : ℕ → G}

theorem fzb_branchB (hβ : FzbChart c T₂ P x₁ x₂ t q s lam β) (hF : FzbFactsGen c)
    {M : Subgroup G} (hM : ∀ x < 1024, β x ∈ M ↔ fzbIsM x) {a : G} (ha : a⁻¹ * t * a ∈ T₂)
    (ha' : a⁻¹ * t * a ∉ M) :
    (∃ b : G, b * (q * s) * b⁻¹ = a⁻¹ * t * a) ∨
      ∃ b : G, b * (q * s * lam) * b⁻¹ = a⁻¹ * t * a := by
  obtain ⟨hq2, hq4, -, h320, h832⟩ := fzb_chart_q hβ hF
  have ht2 : t * t = 1 := by
    calc t * t = q ^ 2 * q ^ 2 := by rw [hq2]
      _ = q ^ (2 + 2) := by rw [pow_add]
      _ = q ^ 4 := by norm_num
      _ = 1 := hq4
  obtain ⟨x, hx, hxβ⟩ := hβ.surj (a⁻¹ * t * a) ha
  have hxM : ¬ fzbIsM x := by
    intro h
    apply ha'
    rw [← hxβ]
    exact (hM x hx).mpr h
  have hsq : fzbMul c x x = 0 := by
    apply hβ.inj _ (hF.mul_lt x hx x hx) 0 (by norm_num)
    rw [hβ.mul x hx x hx, hxβ, hβ.one]
    calc (a⁻¹ * t * a) * (a⁻¹ * t * a) = a⁻¹ * (t * t) * a := by group
      _ = 1 := by rw [ht2]; group
  obtain ⟨g, hg, hgx⟩ := hF.V2 x hx hxM hsq
  have hconj := fzb_chart_conj hβ hF.mul_lt hg hx (show (320 : ℕ) < 1024 by norm_num)
  have hconj2 := fzb_chart_conj hβ hF.mul_lt hg hx (show (832 : ℕ) < 1024 by norm_num)
  rcases hgx with h | h
  · left
    refine ⟨(β g)⁻¹, ?_⟩
    have hmain : β g * β x * (β g)⁻¹ = q * s := by
      rw [← h320]
      exact hconj.mp h
    rw [inv_inv, ← hmain, ← hxβ]
    group
  · right
    refine ⟨(β g)⁻¹, ?_⟩
    have hmain : β g * β x * (β g)⁻¹ = q * s * lam := by
      rw [← h832]
      exact hconj2.mp h
    rw [inv_inv, ← hmain, ← hxβ]
    group

theorem fzb_u_conj_t (hβ : FzbChart c T₂ P x₁ x₂ t q s lam β) (hF : FzbFactsGen c)
    {M : Subgroup G} (hM : ∀ x < 1024, β x ∈ M ↔ fzbIsM x) {a : G} (ha : a⁻¹ * t * a ∈ T₂)
    (ha' : a⁻¹ * t * a ∉ M) (hA5 : ∃ d : G, d * (q * s) * d⁻¹ = q * s * lam) :
    ∃ g : G, g⁻¹ * t * g = q * s * lam := by
  obtain ⟨d, hd⟩ := hA5
  rcases fzb_branchB hβ hF hM ha ha' with ⟨b, hb⟩ | ⟨b, hb⟩
  · refine ⟨a * b * d⁻¹, ?_⟩
    have hqs : q * s = b⁻¹ * (a⁻¹ * t * a) * b := by rw [← hb]; group
    rw [← hd, hqs]
    group
  · refine ⟨a * b, ?_⟩
    have hqsy : q * s * lam = b⁻¹ * (a⁻¹ * t * a) * b := by rw [← hb]; group
    rw [hqsy]
    group

end CFSG.OddStandard.SmallF3.FritzII
