module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2UniqWAux
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_card_le_two_mul {H P : Subgroup G} (hHP : H ≤ P)
    (hcard : Nat.card P ≤ 2 * Nat.card H) : P ≤ normalizer (H : Set G) := by
  set K : Subgroup ↥P := H.subgroupOf P with hK
  have hKcard : Nat.card K = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHP).toEquiv
  have hmul := Subgroup.card_mul_index K
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hidx : K.index ≤ 2 := by
    rw [hKcard] at hmul
    by_contra hlt
    have h3 : 3 ≤ K.index := by omega
    have : Nat.card H * 3 ≤ Nat.card H * K.index := Nat.mul_le_mul_left _ h3
    omega
  have hne : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hnorm : K.Normal := by
    rcases (by omega : K.index = 1 ∨ K.index = 2) with h1 | h2
    · rw [Subgroup.index_eq_one] at h1
      rw [h1]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h2
  have key : ∀ y ∈ P, ∀ h ∈ H, y * h * y⁻¹ ∈ H := by
    intro y hy h hh
    have := hnorm.conj_mem ⟨h, hHP hh⟩ (mem_subgroupOf.2 hh) ⟨y, hy⟩
    exact mem_subgroupOf.1 this
  intro x hx
  rw [mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key x hx h hh, fun hh => ?_⟩
  have := key x⁻¹ (P.inv_mem hx) _ hh
  simpa [mul_assoc] using this

theorem exists_mem_normalizer_conj_of_isSylowOf_top {X X₂ H : Subgroup G}
    (hX : IsSylowOf 2 X (⊤ : Subgroup G)) (hX₂ : IsSylowOf 2 X₂ (⊤ : Subgroup G))
    (h1 : X ≤ normalizer (H : Set G)) (h2 : X₂ ≤ normalizer (H : Set G)) :
    ∃ n ∈ normalizer (H : Set G), ∀ x : G, x ∈ X₂ ↔ n⁻¹ * x * n ∈ X :=
  (hX.of_le h1 le_top).exists_mem_conj (hX₂.of_le h2 le_top)

theorem card_le_two_mul_centralizer {X : Subgroup G} {π q : G}
    (hq : ∀ x ∈ X, x * q = q * x) (hq2 : q * q = 1)
    (hcl : ∀ x ∈ X, x⁻¹ * π * x = π ∨ x⁻¹ * π * x = q * π) :
    Nat.card X ≤ 2 * Nat.card ↥(X ⊓ centralizer ({π} : Set G)) := by
  classical
  have hcent : ∀ x ∈ X, x⁻¹ * π * x = π → x ∈ X ⊓ centralizer ({π} : Set G) := by
    intro x hx h
    refine ⟨hx, mem_centralizer_singleton_iff.2 ?_⟩
    calc x * π = x * (x⁻¹ * π * x) := by rw [h]
      _ = π * x := by group
  by_cases hex : ∃ x₀ ∈ X, x₀⁻¹ * π * x₀ ≠ π
  · obtain ⟨x₀, hx₀, hne⟩ := hex
    have h0 : x₀⁻¹ * π * x₀ = q * π := (hcl x₀ hx₀).resolve_left hne
    have h0' : x₀ * π * x₀⁻¹ = q * π := by
      have hqc : x₀ * q * x₀⁻¹ = q := by
        calc x₀ * q * x₀⁻¹ = (x₀ * q) * x₀⁻¹ := rfl
          _ = (q * x₀) * x₀⁻¹ := by rw [hq x₀ hx₀]
          _ = q := by group
      have h1 : π = q * (x₀ * π * x₀⁻¹) := by
        calc π = x₀ * (x₀⁻¹ * π * x₀) * x₀⁻¹ := by group
          _ = x₀ * (q * π) * x₀⁻¹ := by rw [h0]
          _ = (x₀ * q * x₀⁻¹) * (x₀ * π * x₀⁻¹) := by group
          _ = q * (x₀ * π * x₀⁻¹) := by rw [hqc]
      calc x₀ * π * x₀⁻¹ = (q * q) * (x₀ * π * x₀⁻¹) := by rw [hq2, one_mul]
        _ = q * (q * (x₀ * π * x₀⁻¹)) := by group
        _ = q * π := by rw [← h1]
    have hcov : ∀ w ∈ X, ∃ v ∈ ({1, x₀} : Finset G), w * v⁻¹ ∈ X ⊓ centralizer ({π} : Set G) := by
      intro w hw
      rcases hcl w hw with h | h
      · exact ⟨1, by simp, by simpa using hcent w hw h⟩
      · refine ⟨x₀, by simp, hcent _ (X.mul_mem hw (X.inv_mem hx₀)) ?_⟩
        have hqc : x₀ * q * x₀⁻¹ = q := by
          calc x₀ * q * x₀⁻¹ = (x₀ * q) * x₀⁻¹ := rfl
            _ = (q * x₀) * x₀⁻¹ := by rw [hq x₀ hx₀]
            _ = q := by group
        calc (w * x₀⁻¹)⁻¹ * π * (w * x₀⁻¹) = x₀ * (w⁻¹ * π * w) * x₀⁻¹ := by group
          _ = x₀ * (q * π) * x₀⁻¹ := by rw [h]
          _ = (x₀ * q * x₀⁻¹) * (x₀ * π * x₀⁻¹) := by group
          _ = q * (q * π) := by rw [hqc, h0']
          _ = (q * q) * π := by group
          _ = π := by rw [hq2, one_mul]
    have := card_le_mul_of_cover (W' := X) (W₀ := X ⊓ centralizer ({π} : Set G)) _ hcov
    have h2 : ({1, x₀} : Finset G).card ≤ 2 := Finset.card_le_two
    exact this.trans (Nat.mul_le_mul_right _ h2)
  · push Not at hex
    have hcov : ∀ w ∈ X, ∃ v ∈ ({1} : Finset G), w * v⁻¹ ∈ X ⊓ centralizer ({π} : Set G) := by
      intro w hw
      exact ⟨1, by simp, by simpa using hcent w hw (hex w hw)⟩
    have := card_le_mul_of_cover (W' := X) (W₀ := X ⊓ centralizer ({π} : Set G)) _ hcov
    simp only [Finset.card_singleton, one_mul] at this
    omega

end CFSG.OddStandard.ChengHeld
