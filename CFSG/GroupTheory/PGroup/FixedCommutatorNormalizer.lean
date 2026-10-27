module

public import Mathlib.GroupTheory.PGroup
import CFSG.GroupTheory.PGroup.LtInfNormalizer

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G]

theorem mem_normalizer_of_commutator_mem_of_centralizer_le {D E Q Z Y : Subgroup G}
    (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hQE : Q ≤ E) (hZE : Z ≤ E)
    (hDY : ∀ d ∈ D, ∀ l ∈ Y, l * d * l⁻¹ * d⁻¹ ∈ Z)
    (hYQ : ∀ l ∈ Y, ∀ x ∈ Q, l * x * l⁻¹ = x)
    (hCE : ∀ e ∈ E, (∀ l ∈ Y, l * e * l⁻¹ = e) → e ∈ Q) {d : G} (hd : d ∈ D)
    (hdE : d ∈ normalizer (E : Set G)) : d ∈ normalizer (Q : Set G) := by
  have hconj : ∀ g ∈ D, g ∈ normalizer (E : Set G) → ∀ x ∈ Q, g * x * g⁻¹ ∈ Q := by
    intro g hg hgE x hx
    have hxE : x ∈ E := hQE hx
    have hgxE : g * x * g⁻¹ ∈ E := (mem_set_normalizer_iff.mp hgE x).mp hxE
    refine hCE (g * x * g⁻¹) hgxE fun l hl => ?_
    have hzE : l * g * l⁻¹ * g⁻¹ ∈ E := hZE (hDY g hg l hl)
    have hxfix : l * x * l⁻¹ = x := hYQ l hl x hx
    have hcomm : (l * g * l⁻¹ * g⁻¹) * (g * x * g⁻¹)
        = (g * x * g⁻¹) * (l * g * l⁻¹ * g⁻¹) := hE _ hzE _ hgxE
    calc
      l * (g * x * g⁻¹) * l⁻¹
          = (l * g * l⁻¹) * (l * x * l⁻¹) * (l * g * l⁻¹)⁻¹ := by group
      _ = (l * g * l⁻¹) * x * (l * g * l⁻¹)⁻¹ := by rw [hxfix]
      _ = (l * g * l⁻¹ * g⁻¹) * (g * x * g⁻¹) * (l * g * l⁻¹ * g⁻¹)⁻¹ := by group
      _ = (g * x * g⁻¹) * (l * g * l⁻¹ * g⁻¹) * (l * g * l⁻¹ * g⁻¹)⁻¹ := by rw [hcomm]
      _ = g * x * g⁻¹ := by group
  refine mem_set_normalizer_iff.mpr fun x => ⟨hconj d hd hdE x, fun hx => ?_⟩
  have h := hconj d⁻¹ (D.inv_mem hd) ((normalizer (E : Set G)).inv_mem hdE)
    (d * x * d⁻¹) hx
  rwa [show d⁻¹ * (d * x * d⁻¹) * (d⁻¹)⁻¹ = x by group] at h

theorem false_of_lt_of_commutator_mem_of_centralizer_le [Finite G] {D E Q Z Y : Subgroup G}
    (hD : IsPGroup 2 D) (hED : E < D) (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hQE : Q ≤ E) (hZE : Z ≤ E)
    (hDY : ∀ d ∈ D, ∀ l ∈ Y, l * d * l⁻¹ * d⁻¹ ∈ Z)
    (hYQ : ∀ l ∈ Y, ∀ x ∈ Q, l * x * l⁻¹ = x)
    (hCE : ∀ e ∈ E, (∀ l ∈ Y, l * e * l⁻¹ = e) → e ∈ Q)
    (hN : D ⊓ normalizer (Q : Set G) ≤ E) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hd, hdnotE⟩ := IsConcreteLE.exists_of_lt (lt_inf_normalizer_of_isPGroup hD hED)
  refine hdnotE (hN (mem_inf.mpr ⟨hd.1, ?_⟩))
  exact mem_normalizer_of_commutator_mem_of_centralizer_le hE hQE hZE hDY hYQ hCE hd.1 hd.2

end CFSG.GroupTheory
