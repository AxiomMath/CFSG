module

public import CFSG.Assembly.Defs
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe
open CFSG.Open Subgroup
variable {V : Type} [Group V]

theorem mem_of_isSubnormal_of_inv {X T : Subgroup V} (h : IsSubnormal X T) {s ρ : V}
    (hs : s ∈ X) (hρ : ρ ∈ T) (hodd : Odd (orderOf ρ)) (hinv : s * ρ * s⁻¹ = ρ⁻¹) : ρ ∈ X := by
  induction h with
  | refl => exact hρ
  | @step X Y T hXY hn _ ih =>
    have hρY : ρ ∈ Y := ih (hXY hs) hρ
    have h1 : ρ⁻¹ * s * ρ ∈ X := by
      have h := hn.conj_mem ⟨s, hXY hs⟩ (mem_subgroupOf.mpr hs) (⟨ρ, hρY⟩ : ↥Y)⁻¹
      simpa using mem_subgroupOf.mp h
    have h2 : ρ⁻¹ * ρ⁻¹ ∈ X := by
      have he : ρ⁻¹ * s * ρ * s⁻¹ = ρ⁻¹ * ρ⁻¹ := by
        calc ρ⁻¹ * s * ρ * s⁻¹ = ρ⁻¹ * (s * ρ * s⁻¹) := by group
          _ = ρ⁻¹ * ρ⁻¹ := by rw [hinv]
      exact he ▸ X.mul_mem h1 (X.inv_mem hs)
    have h3 : ρ ^ 2 ∈ X := by
      have h := X.inv_mem h2
      rwa [mul_inv_rev, inv_inv, ← pow_two] at h
    obtain ⟨k, hk⟩ := hodd
    have he : ρ = (ρ ^ 2) ^ (k + 1) := by
      rw [← pow_mul, show 2 * (k + 1) = orderOf ρ + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    rw [he]
    exact X.pow_mem h3 _

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe
end
