module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.CyclicNormalizerDerivedCentralizer

open Subgroup

open scoped commutatorElement

theorem commutator_normalizer_le_centralizer {G : Type*} [Group G] (X : Subgroup G)
    [IsCyclic X] :
    ⁅Subgroup.normalizer (X : Set G), Subgroup.normalizer (X : Set G)⁆ ≤
      Subgroup.centralizer (X : Set G) := by
  have mulAut_comm_of_cyclic (φ ψ : MulAut X) :
      φ * ψ = ψ * φ := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := X)
    have key : ∀ (φ ψ : MulAut X), (φ * ψ) g = (ψ * φ) g := by
      intro φ ψ
      obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 (hg (φ g) |> fun h => by simpa [Subgroup.mem_zpowers_iff] using h)
      obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.1 (hg (ψ g) |> fun h => by simpa [Subgroup.mem_zpowers_iff] using h)
      show φ (ψ g) = ψ (φ g)
      rw [← hb, ← ha]
      simp only [map_zpow]
      rw [← ha, ← hb, ← zpow_mul, ← zpow_mul, mul_comm]
    ext x
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg x |> fun h => by simpa [Subgroup.mem_zpowers_iff] using h)
    have := key φ ψ
    simp only [MulAut.mul_apply] at this ⊢
    simp [map_zpow, this]
  rw [Subgroup.commutator_le]
  intro n hn m hm
  have hcomm : X.normalizerMonoidHom ⁅(⟨n, hn⟩ : Subgroup.normalizer (X : Set G)),
      (⟨m, hm⟩ : Subgroup.normalizer (X : Set G))⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact mulAut_comm_of_cyclic _ _
  have hker : ⁅(⟨n, hn⟩ : Subgroup.normalizer (X : Set G)), (⟨m, hm⟩ : Subgroup.normalizer (X : Set G))⁆ ∈ X.normalizerMonoidHom.ker := hcomm
  rw [Subgroup.normalizerMonoidHom_ker] at hker
  exact hker

end CFSG.GroupTheory.CoprimeActionSupport.CyclicNormalizerDerivedCentralizer
