module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutCoprime

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem fpf_section_of_fixed {U W : Subgroup G} {ρ : G} (hρ3 : ρ ^ 3 = 1)
    (hρU : ∀ u ∈ U, ρ * u * ρ⁻¹ ∈ U) (hUW : U ≤ W)
    (hUn : ∀ w ∈ W, ∀ u ∈ U, w * u * w⁻¹ ∈ U) (h3 : ¬ 3 ∣ Nat.card U)
    (hfix : ∀ x ∈ W, ρ * x * ρ⁻¹ = x → x ∈ U) :
    ∀ w ∈ W, ρ * w * ρ⁻¹ * w⁻¹ ∈ U → w ∈ U := by
  intro w hwW hc
  have hρ3A : (MulAut.conj ρ) ^ 3 = 1 := by
    rw [← map_pow, hρ3, map_one]
  have hA : ∀ a ∈ U, (MulAut.conj ρ) a ∈ U := by
    intro a ha
    rw [MulAut.conj_apply]
    exact hρU a ha
  have ht : w⁻¹ * (MulAut.conj ρ) w ∈ U := by
    have h1 : w⁻¹ * (MulAut.conj ρ) w = w⁻¹ * (ρ * w * ρ⁻¹ * w⁻¹) * w := by
      rw [MulAut.conj_apply]; group
    rw [h1]
    simpa using hUn w⁻¹ (inv_mem hwW) (ρ * w * ρ⁻¹ * w⁻¹) hc
  obtain ⟨s, hs, hfixs⟩ :=
    CFSG.OddStandard.SmallF3.HarrisU33.Outside.exists_fixed_in_coset_of_not_dvd
      (MulAut.conj ρ) hρ3A U hA h3 w ht
  rw [MulAut.conj_apply] at hfixs
  have hsW : s ∈ W := by
    have h2 : s = w * (w⁻¹ * s) := by group
    rw [h2]
    exact mul_mem hwW (hUW hs)
  have hsU : s ∈ U := hfix s hsW hfixs
  have hw : w = s * (w⁻¹ * s)⁻¹ := by group
  rw [hw]
  exact mul_mem hsU (inv_mem hs)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
