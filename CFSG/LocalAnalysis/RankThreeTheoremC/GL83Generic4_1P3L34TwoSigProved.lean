module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34MKlein
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Proved
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

theorem l34TwoSignalizer_proved :
    KFactL34TwoSignalizer := by
  intro K _ _ hL Q
  obtain ⟨-, -, hmax, -⟩ := kFactL34Three K hL Q
  have hel := l34SylowElemAbelian hL Q
  have hcard := l34SylowCard hL Q
  refine ⟨hel, fun u huQ hu3 => ?_⟩
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu3
    exact absurd hu3 (by norm_num)
  obtain ⟨b, hbQ, hb1, x₀, y₀, hx₀, hy₀, hxy₀, hbx, hby, hxN⟩ := l34KleinOfSylow hL Q
  obtain ⟨n, hn, hnb⟩ := kFactL34SylowTransitive K hL Q b u hbQ huQ hb1 hu1
  have hrank : 1 ≤ CFSG.Open.pRank 3 (Q : Subgroup K) :=
    (show 1 ≤ 2 by norm_num).trans
      (pRank_ge_of_elemAbelian_card (by norm_num) le_rfl hel (by rw [hcard]; norm_num))
  refine top_le_gamma_sup_of_klein (x := n * x₀ * n⁻¹) (y := n * y₀ * n⁻¹) hrank hmax
    ?_ ?_ ?_ ?_ ?_ ?_
  · calc n * x₀ * n⁻¹ * (n * x₀ * n⁻¹) = n * (x₀ * x₀) * n⁻¹ := by group
      _ = 1 := by rw [hx₀]; group
  · calc n * y₀ * n⁻¹ * (n * y₀ * n⁻¹) = n * (y₀ * y₀) * n⁻¹ := by group
      _ = 1 := by rw [hy₀]; group
  · calc n * x₀ * n⁻¹ * (n * y₀ * n⁻¹) = n * (x₀ * y₀) * n⁻¹ := by group
      _ = n * (y₀ * x₀) * n⁻¹ := by rw [hxy₀]
      _ = n * y₀ * n⁻¹ * (n * x₀ * n⁻¹) := by group
  · rw [← hnb]
    calc n * b * n⁻¹ * (n * x₀ * n⁻¹) * (n * b * n⁻¹)⁻¹ = n * (b * x₀ * b⁻¹) * n⁻¹ := by group
      _ = n * y₀ * n⁻¹ := by rw [hbx]
  · rw [← hnb]
    calc n * b * n⁻¹ * (n * y₀ * n⁻¹) * (n * b * n⁻¹)⁻¹ = n * (b * y₀ * b⁻¹) * n⁻¹ := by group
      _ = n * (x₀ * y₀) * n⁻¹ := by rw [hby]
      _ = n * x₀ * n⁻¹ * (n * y₀ * n⁻¹) := by group
  · intro hN
    apply hxN
    have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hn) hN) hn
    simpa [mul_assoc] using this

end CFSG.LocalAnalysis.RankThreeTheoremC
