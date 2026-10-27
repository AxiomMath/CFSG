module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.GroupTheory.HuppertProduct

variable {G : Type*} [Group G]

theorem card_mul_relIndex_le [Finite G] {H M E : Subgroup G} {Δ : Type*} [Group Δ]
    (φ : H →* Δ) (hφ : Function.Surjective φ) (hMH : M ≤ H) (hEH : E ≤ H)
    (hM : ∀ x : H, (x : G) ∈ M → φ x = 1) (hE : ∀ x : H, (x : G) ∈ E → φ x = 1) :
    Nat.card Δ * M.relIndex E ≤ M.relIndex H := by
  set N : Subgroup G := φ.ker.map H.subtype with hN
  have hNH : N ≤ H := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hMN : M ≤ N := fun m hm => ⟨⟨m, hMH hm⟩, (MonoidHom.mem_ker).2 (hM _ hm), rfl⟩
  have hEN : E ≤ N := fun e he => ⟨⟨e, hEH he⟩, (MonoidHom.mem_ker).2 (hE _ he), rfl⟩
  have hsub : N.subgroupOf H = φ.ker :=
    Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
  have hΔ : Nat.card Δ = N.relIndex H := by
    rw [Subgroup.relIndex, hsub, Subgroup.index_eq_card]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv).symm
  have hne : M.relIndex N ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : M.relIndex E ≤ M.relIndex N := Subgroup.relIndex_le_of_le_right hEN hne
  have h2 : M.relIndex N * N.relIndex H = M.relIndex H :=
    Subgroup.relIndex_mul_relIndex M N H hMN hNH
  calc Nat.card Δ * M.relIndex E = N.relIndex H * M.relIndex E := by rw [hΔ]
    _ ≤ N.relIndex H * M.relIndex N := Nat.mul_le_mul_left _ h1
    _ = M.relIndex N * N.relIndex H := mul_comm _ _
    _ = M.relIndex H := h2

end CFSG.GroupTheory.HuppertProduct
