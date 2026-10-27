module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsU33Abs

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.U33

open scoped commutatorElement

variable {Γ Γ' : Type*} [Group Γ] [Group Γ']

@[expose] def canZ (S : Subgroup Γ) : Subgroup Γ := S ⊓ Subgroup.centralizer (S : Set Γ)

@[expose] def canK1 (S : Subgroup Γ) : Subgroup Γ := Subgroup.centralizer (canZ S : Set Γ)

@[expose] def canA (S : Subgroup Γ) : Subgroup Γ :=
  S ⊓ Subgroup.centralizer ((⁅S, S⁆ : Subgroup Γ) : Set Γ)

@[expose] def canK2 (S : Subgroup Γ) : Subgroup Γ := Subgroup.normalizer (canA S : Set Γ)

theorem mem_map_equiv_iff (σ : Γ ≃* Γ') (H : Subgroup Γ) (x : Γ) :
    σ x ∈ H.map σ.toMonoidHom ↔ x ∈ H := by
  simp

theorem mem_centralizer_image_iff (σ : Γ ≃* Γ') (X : Set Γ) (x : Γ) :
    σ x ∈ Subgroup.centralizer (σ '' X) ↔ x ∈ Subgroup.centralizer X := by
  simp only [Subgroup.mem_centralizer_iff, Set.forall_mem_image, ← map_mul,
    EmbeddingLike.apply_eq_iff_eq]

theorem mem_normalizer_map_iff (σ : Γ ≃* Γ') (H : Subgroup Γ) (x : Γ) :
    σ x ∈ Subgroup.normalizer ((H.map σ.toMonoidHom : Subgroup Γ') : Set Γ') ↔
      x ∈ Subgroup.normalizer (H : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have := h (σ y)
    rwa [mem_map_equiv_iff, ← map_inv, ← map_mul, ← map_mul, mem_map_equiv_iff] at this
  · intro h y'
    obtain ⟨y, rfl⟩ := σ.surjective y'
    rw [mem_map_equiv_iff, ← map_inv, ← map_mul, ← map_mul, mem_map_equiv_iff]
    exact h y

theorem canZ_map (σ : Γ ≃* Γ') (S : Subgroup Γ) :
    canZ (S.map σ.toMonoidHom) = (canZ S).map σ.toMonoidHom := by
  ext y
  obtain ⟨x, rfl⟩ := σ.surjective y
  rw [mem_map_equiv_iff, canZ, canZ, Subgroup.mem_inf, Subgroup.mem_inf, mem_map_equiv_iff,
    Subgroup.coe_map]
  exact and_congr_right fun _ => mem_centralizer_image_iff σ _ x

theorem canK1_map (σ : Γ ≃* Γ') (S : Subgroup Γ) :
    canK1 (S.map σ.toMonoidHom) = (canK1 S).map σ.toMonoidHom := by
  ext y
  obtain ⟨x, rfl⟩ := σ.surjective y
  rw [mem_map_equiv_iff, canK1, canK1, canZ_map, Subgroup.coe_map]
  exact mem_centralizer_image_iff σ _ x

theorem canA_map (σ : Γ ≃* Γ') (S : Subgroup Γ) :
    canA (S.map σ.toMonoidHom) = (canA S).map σ.toMonoidHom := by
  ext y
  obtain ⟨x, rfl⟩ := σ.surjective y
  rw [mem_map_equiv_iff, canA, canA, Subgroup.mem_inf, Subgroup.mem_inf, mem_map_equiv_iff,
    ← Subgroup.map_commutator, Subgroup.coe_map]
  exact and_congr_right fun _ => mem_centralizer_image_iff σ _ x

theorem canK2_map (σ : Γ ≃* Γ') (S : Subgroup Γ) :
    canK2 (S.map σ.toMonoidHom) = (canK2 S).map σ.toMonoidHom := by
  ext y
  obtain ⟨x, rfl⟩ := σ.surjective y
  rw [mem_map_equiv_iff, canK2, canK2, canA_map]
  exact mem_normalizer_map_iff σ _ x

theorem mem_canK1_of_map_eq (σ : Γ ≃* Γ) {S : Subgroup Γ} (hS : S.map σ.toMonoidHom = S) {x : Γ}
    (hx : x ∈ canK1 S) : σ x ∈ canK1 S := by
  have := canK1_map σ S
  rw [hS] at this
  rw [this]
  exact Subgroup.mem_map_of_mem _ hx

theorem mem_canK2_of_map_eq (σ : Γ ≃* Γ) {S : Subgroup Γ} (hS : S.map σ.toMonoidHom = S) {x : Γ}
    (hx : x ∈ canK2 S) : σ x ∈ canK2 S := by
  have := canK2_map σ S
  rw [hS] at this
  rw [this]
  exact Subgroup.mem_map_of_mem _ hx

end CFSG.QuasithinUnique.Vol2Native.L239.U33
