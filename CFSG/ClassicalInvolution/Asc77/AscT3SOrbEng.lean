module

public import CFSG.ClassicalInvolution.Asc77.WP3LayerHyp
public import CFSG.ClassicalInvolution.Asc77.AscT3SConfEng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Cases

variable {G : Type} [Group G]

theorem closure_three_cases {z t a c : G} (hz : z * z = 1) (ht : t * t = 1) (ha : a * a = 1)
    (hzt : z * t = t * z) (hza : z * a = a * z) (hta : t * a = a * t)
    (hc : c ∈ Subgroup.closure ({z, t, a} : Set G)) :
    (c = 1 ∨ c = z ∨ c = t ∨ c = z * t) ∨ (c = a ∨ c = z * a ∨ c = t * a ∨ c = z * t * a) := by
  have hcl : Subgroup.closure ({z, t, a} : Set G) =
      Subgroup.closure ({z, t} : Set G) ⊔ Subgroup.zpowers a := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro v hv
      rcases hv with rfl | rfl | rfl
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · refine sup_le ?_ (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
      rw [Subgroup.closure_le]
      intro v hv
      rcases hv with rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
  have hcomm : Commutes (Subgroup.closure ({z, t} : Set G)) (Subgroup.zpowers a) := by
    have hle : Subgroup.closure ({z, t} : Set G) ≤ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.closure_le]
      intro v hv
      rcases hv with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hza
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hta
    intro v hv u hu
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have : Commute v a := Subgroup.mem_centralizer_singleton_iff.mp (hle hv)
    exact (this.zpow_right i).eq
  rw [hcl] at hc
  obtain ⟨y, hy, w, hw, rfl⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hcomm hc
  rcases eq_one_or_eq_of_mem_zpowers ha hw with h1 | h1
  · left
    rw [h1, mul_one]
    exact closure_pair_cases hz ht hzt hy
  · right
    rw [h1]
    rcases closure_pair_cases hz ht hzt hy with h2 | h2 | h2 | h2
    · left; rw [h2, one_mul]
    · right; left; rw [h2]
    · right; right; left; rw [h2]
    · right; right; right; rw [h2]

end Cases

section OrbEngine

variable {G : Type} [Group G] [Finite G] {z t a : G}

theorem s_hyp51_of_at_of
    (hρ : ∃ ρ : G, a * ρ = ρ * a ∧ ρ * z * ρ⁻¹ = z * t ∧ ρ * t * ρ⁻¹ = z ∧
      ρ ∈ Subgroup.normalizer ((Subgroup.closure ({z, t, a} : Set G) : Subgroup G) : Set G))
    (hz2 : z * z = 1) (ht2 : t * t = 1) (ha2 : a * a = 1) (hzt : z * t = t * z)
    (hza : z * a = a * z) (hta : t * a = a * t)
    (hB : IsElemAbelian 2 (Subgroup.closure ({z, t, a} : Set G)))
    (hcard : Nat.card ↥(Subgroup.closure ({z, t, a} : Set G)) = 8)
    (hz : Hyp51At (Subgroup.closure ({z, t, a} : Set G)) z)
    (ha : Hyp51At (Subgroup.closure ({z, t, a} : Set G)) a)
    (haz : Hyp51At (Subgroup.closure ({z, t, a} : Set G)) (a * z)) :
    Hyp51 (Subgroup.closure ({z, t, a} : Set G)) := by
  obtain ⟨ρ, hρa, hρz, hρt, hρN⟩ := hρ
  have hρa' : ρ * a * ρ⁻¹ = a := mul_inv_eq_iff_eq_mul.mpr hρa.symm
  have hρzt : ρ * (z * t) * ρ⁻¹ = t := by
    calc ρ * (z * t) * ρ⁻¹ = (ρ * z * ρ⁻¹) * (ρ * t * ρ⁻¹) := by group
      _ = (z * t) * z := by rw [hρz, hρt]
      _ = z * (t * z) := by group
      _ = z * (z * t) := by rw [hzt]
      _ = t := by rw [← mul_assoc, hz2, one_mul]
  have hρρz : (ρ * ρ) * z * (ρ * ρ)⁻¹ = t := by
    calc (ρ * ρ) * z * (ρ * ρ)⁻¹ = ρ * (ρ * z * ρ⁻¹) * ρ⁻¹ := by group
      _ = t := by rw [hρz, hρzt]
  have hρρa : (ρ * ρ) * a * (ρ * ρ)⁻¹ = a := by
    calc (ρ * ρ) * a * (ρ * ρ)⁻¹ = ρ * (ρ * a * ρ⁻¹) * ρ⁻¹ := by group
      _ = a := by rw [hρa', hρa']
  have hρN2 : ρ * ρ ∈ Subgroup.normalizer
      ((Subgroup.closure ({z, t, a} : Set G) : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ hρN hρN
  have hzmem : z ∈ ({z, a, a * z} : Set G) := by simp
  have hamem : a ∈ ({z, a, a * z} : Set G) := by simp
  have hazmem : a * z ∈ ({z, a, a * z} : Set G) := by simp
  refine ExactLayer.hyp51_of_orbitReps (R := ({z, a, a * z} : Set G))
    hB hcard ?_ ?_
  · intro r hr
    rcases hr with rfl | rfl | rfl
    · exact hz
    · exact ha
    · exact haz
  · intro c hc hc1
    rcases closure_three_cases hz2 ht2 ha2 hzt hza hta hc with
      (h1 | h1 | h1 | h1) | (h1 | h1 | h1 | h1)
    · exact absurd h1 hc1
    · exact ⟨z, hzmem, 1, Subgroup.one_mem _, by rw [h1]; group⟩
    · exact ⟨z, hzmem, ρ * ρ, hρN2, by rw [h1, hρρz]⟩
    · exact ⟨z, hzmem, ρ, hρN, by rw [h1, hρz]⟩
    · exact ⟨a, hamem, 1, Subgroup.one_mem _, by rw [h1]; group⟩
    · exact ⟨a * z, hazmem, 1, Subgroup.one_mem _, by rw [h1, hza]; group⟩
    · refine ⟨a * z, hazmem, ρ * ρ, hρN2, ?_⟩
      calc c = a * t := by rw [h1, hta]
        _ = ((ρ * ρ) * a * (ρ * ρ)⁻¹) * ((ρ * ρ) * z * (ρ * ρ)⁻¹) := by rw [hρρa, hρρz]
        _ = (ρ * ρ) * (a * z) * (ρ * ρ)⁻¹ := by group
    · refine ⟨a * z, hazmem, ρ, hρN, ?_⟩
      calc c = a * (z * t) := by
            rw [h1]
            calc z * t * a = z * (t * a) := by group
              _ = z * (a * t) := by rw [hta]
              _ = (z * a) * t := by group
              _ = (a * z) * t := by rw [hza]
              _ = a * (z * t) := by group
        _ = (ρ * a * ρ⁻¹) * (ρ * z * ρ⁻¹) := by rw [hρa', hρz]
        _ = ρ * (a * z) * ρ⁻¹ := by group

end OrbEngine

end CFSG.ClassicalInvolution.Asc77.T3CII
