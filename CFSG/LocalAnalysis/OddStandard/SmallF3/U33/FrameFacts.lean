module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Model28

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.GH74.KGroups.U33
  CFSG.OddStandard.SmallF3.HarrisU33.K28

section KLevel

variable
  {K : Type} [Group K]

private theorem outer_not_mem_P (m : Model28 K) {γ : MulAut K}
    (hγ' : ∀ k : K, γ ≠ MulAut.conj k) : m.ι γ ∉ QP.originalSubgroup := by
  intro hmem
  obtain ⟨k, hk⟩ := m.exists_ε hmem
  apply hγ' k
  apply m.ι_injective
  rw [m.ι_conj k]
  exact hk.symm

private theorem exists_conj_ftau_of_outer (m : Model28 K) {γ : MulAut K}
    (hγ : γ * γ = 1) (hγ' : ∀ k : K, γ ≠ MulAut.conj k) :
    ∃ c ∈ QP.originalSubgroup, c * ftau * c⁻¹ = m.ι γ := by
  have hγA : m.ι γ ∈ QA.originalSubgroup := m.ι_mem γ
  have hγP : m.ι γ ∉ QP.originalSubgroup := outer_not_mem_P m hγ'
  have hγ2 : m.ι γ * m.ι γ = 1 := by rw [← map_mul, hγ, map_one]
  exact outer_invol_conj_ftau hγA hγP hγ2

theorem card_K_of_psu33 (h : LieModel K .PSU 3 3 1) : Nat.card K = 6048 := by
  obtain ⟨m⟩ := exists_model28 h
  exact m.card_K

theorem card_aut_of_psu33 (h : LieModel K .PSU 3 3 1) : Nat.card (MulAut K) = 2 * 6048 := by
  obtain ⟨m⟩ := exists_model28 h
  rw [m.card_aut]

theorem conj_injective_of_psu33 (h : LieModel K .PSU 3 3 1) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  obtain ⟨m⟩ := exists_model28 h
  rw [injective_iff_map_eq_one]
  intro k hk
  have h1 : m.ε k = 1 := by
    rw [← m.ι_conj k, hk, map_one]
  exact m.ε_injective (by rw [h1, map_one])

theorem invol_conj_of_psu33 (h : LieModel K .PSU 3 3 1) {g g' : K} (hg : g * g = 1) (hg1 : g ≠ 1)
    (hg' : g' * g' = 1) (hg1' : g' ≠ 1) : ∃ c : K, c * g * c⁻¹ = g' := by
  obtain ⟨m⟩ := exists_model28 h
  have hg2 : m.ε g * m.ε g = 1 := by rw [← map_mul, hg, map_one]
  have hg1m : m.ε g ≠ 1 := fun hh => hg1 (m.ε_injective (by rw [hh, map_one]))
  have hg'2 : m.ε g' * m.ε g' = 1 := by rw [← map_mul, hg', map_one]
  have hg1'm : m.ε g' ≠ 1 := fun hh => hg1' (m.ε_injective (by rw [hh, map_one]))
  obtain ⟨c₁, hc₁, hc₁'⟩ := invol_conj_fz (m.ε_mem g) hg2 hg1m
  obtain ⟨c₂, hc₂, hc₂'⟩ := invol_conj_fz (m.ε_mem g') hg'2 hg1'm
  obtain ⟨c, hc⟩ := m.exists_ε (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc₂) hc₁)
  refine ⟨c, ?_⟩
  apply m.ε_injective
  rw [map_mul, map_mul, map_inv, hc]
  have hgg : m.ε g' = c₂⁻¹ * fz * c₂ := by rw [← hc₂']; group
  rw [hgg, ← hc₁']
  group

theorem outer_invol_conj_of_psu33 (h : LieModel K .PSU 3 3 1) {α β : MulAut K}
    (hα : α * α = 1) (hα' : ∀ k : K, α ≠ MulAut.conj k) (hβ : β * β = 1)
    (hβ' : ∀ k : K, β ≠ MulAut.conj k) :
    ∃ k : K, β = MulAut.conj k * α * (MulAut.conj k)⁻¹ := by
  obtain ⟨m⟩ := exists_model28 h
  obtain ⟨cα, hcα_mem, hcα⟩ := exists_conj_ftau_of_outer m hα hα'
  obtain ⟨cβ, hcβ_mem, hcβ⟩ := exists_conj_ftau_of_outer m hβ hβ'
  let c : Pm := cβ * cα⁻¹
  have hc_mem : c ∈ QP.originalSubgroup :=
    Subgroup.mul_mem _ hcβ_mem (Subgroup.inv_mem _ hcα_mem)
  have hc_conj : c * m.ι α * c⁻¹ = m.ι β := by
    rw [show m.ι α = cα * ftau * cα⁻¹ from hcα.symm, ← hcβ]
    dsimp only [c]
    group
  obtain ⟨k, hk⟩ := m.exists_ε hc_mem
  refine ⟨k, ?_⟩
  apply m.ι_injective
  rw [map_mul, map_mul, map_inv, m.ι_conj k, hk]
  exact hc_conj.symm

end KLevel

end CFSG.OddStandard.SmallF3.HarrisU33
