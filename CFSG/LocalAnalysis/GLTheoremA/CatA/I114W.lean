module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Lem
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Ind

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

open CFSG.Open

variable {Y : Type} [Group Y]

@[expose] def WU (x : Y) (U : Subgroup Y) : Subgroup Y := U ⊔ cj x U ⊔ cj (x * x) U

theorem cent_cj {L : Subgroup Y} {x β : Y} (hβx : β * x = x * β) (hβ : Cent L β) :
    Cent (cj x L) β := by
  intro l hl
  rw [mem_cj] at hl
  have hk := hβ _ hl
  have hxinv : x⁻¹ * β = β * x⁻¹ := by
    have : x⁻¹ * (β * x) * x⁻¹ = x⁻¹ * (x * β) * x⁻¹ := by rw [hβx]
    calc x⁻¹ * β = x⁻¹ * (β * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * β) * x⁻¹ := this
      _ = β * x⁻¹ := by group
  calc l * β = x * (x⁻¹ * l * x) * x⁻¹ * β := by group
    _ = x * (x⁻¹ * l * x) * (β * x⁻¹) := by rw [← hxinv]; group
    _ = x * ((x⁻¹ * l * x) * β) * x⁻¹ := by group
    _ = x * (β * (x⁻¹ * l * x)) * x⁻¹ := by rw [hk]
    _ = β * (x * (x⁻¹ * l * x) * x⁻¹) := by
      calc x * (β * (x⁻¹ * l * x)) * x⁻¹ = (x * β) * (x⁻¹ * l * x) * x⁻¹ := by group
        _ = (β * x) * (x⁻¹ * l * x) * x⁻¹ := by rw [hβx]
        _ = β * (x * (x⁻¹ * l * x) * x⁻¹) := by group
    _ = β * l := by group

theorem cj_comm_cj {x m : Y} {U : Subgroup Y} (hmx : m * x = x * m) :
    cj m (cj x U) = cj x (cj m U) := by
  rw [← cj_mul, ← cj_mul, hmx]

theorem mem_normalizer_WU {x g : Y} {U : Subgroup Y} (h1 : cj g U = U)
    (h2 : cj g (cj x U) = cj x U) (h3 : cj g (cj (x * x) U) = cj (x * x) U) :
    g ∈ Subgroup.normalizer ((WU x U : Subgroup Y) : Set Y) := by
  rw [mem_normalizer_iff_cj, WU, cj_sup, cj_sup, h1, h2, h3]

theorem mem_normalizer_WU_of_cent {K : Subgroup Y} {x g : Y} {U : Subgroup Y} (hUK : U ≤ K)
    (hgK : Cent K g) (hgK₂ : Cent (cj x K) g) (hgK₃ : Cent (cj (x * x) K) g) :
    g ∈ Subgroup.normalizer ((WU x U : Subgroup Y) : Set Y) := by
  apply mem_normalizer_WU
  · exact cj_eq_of_cent (cent_of_le hUK hgK)
  · exact cj_eq_of_cent (cent_of_le (cj_mono x hUK) hgK₂)
  · exact cj_eq_of_cent (cent_of_le (cj_mono (x * x) hUK) hgK₃)

end CFSG.LocalAnalysis.GLTheoremA.I114
