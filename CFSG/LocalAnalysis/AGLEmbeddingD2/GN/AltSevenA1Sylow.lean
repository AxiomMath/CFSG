module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.AltSevenA1SylowData

public section

namespace CFSG.AGLEmbeddingD2.GN

open Equiv Equiv.Perm

section Normalizer

theorem mem_of_normalizes_of_sylow {S : Subgroup (alternatingGroup (Fin 7))} (hS : IsPGroup 2 S)
    (hodd : ¬ 2 ∣ S.index) {g : alternatingGroup (Fin 7)} (h1 : ∀ h ∈ S, g * h * g⁻¹ ∈ S)
    (h2 : ∀ h ∈ S, g⁻¹ * h * g ∈ S) : g ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7))
    (isPGroup_a7SylSub.toSylow not_two_dvd_index_a7SylSub) (hS.toSylow hodd)
  have hmem : ∀ x, x ∈ S ↔ a⁻¹ * x * a ∈ a7SylSub := by
    intro x
    have h0 : (S : Subgroup (alternatingGroup (Fin 7))) =
        ((a • isPGroup_a7SylSub.toSylow not_two_dvd_index_a7SylSub : Sylow 2 _) : Subgroup _) := by
      rw [ha, IsPGroup.toSylow_coe]
    rw [h0, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      IsPGroup.toSylow_coe]
    simp
  have hg1 : ∀ h ∈ a7SylSub, (a⁻¹ * g * a) * h * (a⁻¹ * g * a)⁻¹ ∈ a7SylSub := by
    intro h hh
    have h3 : a * h * a⁻¹ ∈ S := by
      rw [hmem, show a⁻¹ * (a * h * a⁻¹) * a = h by group]
      exact hh
    have h4 := (hmem _).1 (h1 _ h3)
    have : (a⁻¹ * g * a) * h * (a⁻¹ * g * a)⁻¹ = a⁻¹ * (g * (a * h * a⁻¹) * g⁻¹) * a := by group
    rw [this]
    exact h4
  have hg2 : ∀ h ∈ a7SylSub, (a⁻¹ * g * a)⁻¹ * h * (a⁻¹ * g * a) ∈ a7SylSub := by
    intro h hh
    have h3 : a * h * a⁻¹ ∈ S := by
      rw [hmem, show a⁻¹ * (a * h * a⁻¹) * a = h by group]
      exact hh
    have h4 := (hmem _).1 (h2 _ h3)
    have : (a⁻¹ * g * a)⁻¹ * h * (a⁻¹ * g * a) = a⁻¹ * (g⁻¹ * (a * h * a⁻¹) * g) * a := by group
    rw [this]
    exact h4
  have := mem_a7SylSub_of_normalizes hg1 hg2
  exact (hmem g).2 this

theorem mem_of_mem_normalizer_of_sylow {S : Subgroup (alternatingGroup (Fin 7))}
    (hS : IsPGroup 2 S) (hodd : ¬ 2 ∣ S.index) {g : alternatingGroup (Fin 7)}
    (hg : g ∈ Subgroup.normalizer (S : Set (alternatingGroup (Fin 7)))) : g ∈ S := by
  refine mem_of_normalizes_of_sylow hS hodd (fun h hh => (Subgroup.mem_normalizer_iff.1 hg h).1 hh)
    (fun h hh => ?_)
  have hg' : g⁻¹ ∈ Subgroup.normalizer (S : Set (alternatingGroup (Fin 7))) := Subgroup.inv_mem _ hg
  simpa using (Subgroup.mem_normalizer_iff.1 hg' h).1 hh

end Normalizer

section FixedPoint

variable {G : Type*} [Group G] [Finite G]

theorem mem_of_smul_sylow_le (P : Sylow 2 G) {H : Subgroup G} (hPH : (P : Subgroup G) ≤ H)
    (hN : ∀ n ∈ Subgroup.normalizer ((P : Subgroup G) : Set G), n ∈ H) {g : G}
    (hg : ((g⁻¹ • P : Sylow 2 G) : Subgroup G) ≤ H) : g ∈ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H (P.subtype hPH) ((g⁻¹ • P).subtype hg)
  have h1 : (h : G) • P = g⁻¹ • P := by
    refine Sylow.subtype_injective (N := H) (hP := Sylow.smul_le hPH h) (hQ := hg) ?_
    exact (Sylow.smul_subtype hPH h).symm.trans hh
  have h2 : (g * (h : G)) • P = P := by
    rw [mul_smul, h1, smul_inv_smul]
  have h3 := hN _ (Sylow.smul_eq_iff_mem_normalizer.1 h2)
  have := H.mul_mem h3 (H.inv_mem h.2)
  simpa using this

end FixedPoint

end CFSG.AGLEmbeddingD2.GN
