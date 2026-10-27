module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYGrp

public section

namespace CFSG.EvenSporadicStandard.HSStd.FiveY

open Subgroup

variable {G : Type*} [Group G]

theorem exists_conj_cent_y {t y x g : G}
    (hP : ∀ a b : G, a ∈ centralizer ({t} : Set G) → b ∈ centralizer ({t} : Set G) →
      orderOf a = 3 → orderOf b = 3 → ∃ n ∈ centralizer ({t} : Set G), n * a * n⁻¹ = b)
    (hyt : y ∈ centralizer ({t} : Set G)) (hy3 : orderOf y = 3) (hyx : y * x = x * y)
    (hg : g * t * g⁻¹ = x) : ∃ g' : G, g' * y = y * g' ∧ g' * t * g'⁻¹ = x := by
  have hgt : g * t = x * g := by
    have := congrArg (· * g) hg
    simpa using this
  have htg : t * g⁻¹ = g⁻¹ * x := by
    calc t * g⁻¹ = g⁻¹ * (g * t) * g⁻¹ := by group
      _ = g⁻¹ * (x * g) * g⁻¹ := by rw [hgt]
      _ = g⁻¹ * x := by group
  have hy₁t : g⁻¹ * y * g ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc g⁻¹ * y * g * t = g⁻¹ * y * (g * t) := by rw [mul_assoc]
      _ = g⁻¹ * (y * x) * g := by rw [hgt]; group
      _ = g⁻¹ * (x * y) * g := by rw [hyx]
      _ = t * g⁻¹ * y * g := by rw [htg]; group
      _ = t * (g⁻¹ * y * g) := by group
  have hy₁3 : orderOf (g⁻¹ * y * g) = 3 := by
    have := (MulAut.conj g⁻¹).orderOf_eq y
    rw [MulAut.conj_apply, inv_inv] at this
    rw [this, hy3]
  obtain ⟨n, hn, hny⟩ := hP _ _ hy₁t hyt hy₁3 hy3
  have hnt : n * t = t * n := mem_centralizer_singleton_iff.1 hn
  refine ⟨g * n⁻¹, ?_, ?_⟩
  · have h1 : g * n⁻¹ * y * n * g⁻¹ = y := by
      have h2 : g⁻¹ * y * g = n⁻¹ * y * n := by
        calc g⁻¹ * y * g = n⁻¹ * (n * (g⁻¹ * y * g) * n⁻¹) * n := by group
          _ = n⁻¹ * y * n := by rw [hny]
      calc g * n⁻¹ * y * n * g⁻¹ = g * (n⁻¹ * y * n) * g⁻¹ := by group
        _ = g * (g⁻¹ * y * g) * g⁻¹ := by rw [h2]
        _ = y := by group
    calc g * n⁻¹ * y = (g * n⁻¹ * y * n * g⁻¹) * (g * n⁻¹) := by group
      _ = y * (g * n⁻¹) := by rw [h1]
  · calc g * n⁻¹ * t * (g * n⁻¹)⁻¹ = g * (n⁻¹ * t * n) * g⁻¹ := by group
      _ = g * t * g⁻¹ := by
          congr 2
          calc n⁻¹ * t * n = n⁻¹ * (t * n) := by rw [mul_assoc]
            _ = n⁻¹ * (n * t) := by rw [hnt]
            _ = t := by group
      _ = x := hg

end CFSG.EvenSporadicStandard.HSStd.FiveY
