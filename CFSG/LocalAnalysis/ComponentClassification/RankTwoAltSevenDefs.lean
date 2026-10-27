module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltPair

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G]

@[expose] def AltCoords (n : ℕ) (A B : Subgroup G) (ψA : A ≃* alternatingGroup (Fin n))
    (ψB : B ≃* alternatingGroup (Fin n)) : Prop :=
  IsSylowOf 2 (((rootV n).map ψA.symm.toMonoidHom).map A.subtype)
      (Subgroup.centralizer (B : Set G)) ∧
    IsSylowOf 2 (((rootV n).map ψB.symm.toMonoidHom).map B.subtype)
      (Subgroup.centralizer (A : Set G)) ∧
    ((rootAlt n).map ψA.symm.toMonoidHom).map A.subtype ≤ Subgroup.centralizer (B : Set G) ∧
    ((rootAlt n).map ψB.symm.toMonoidHom).map B.subtype ≤ Subgroup.centralizer (A : Set G) ∧
    (∀ x : A, (∀ i : Fin n, (i : ℕ) < 4 → ((ψA x : Perm (Fin n)) i : ℕ) < 4) →
      ∀ b : B, ∃ hb : (x : G) * b * (x : G)⁻¹ ∈ B,
        (ψB ⟨_, hb⟩ : Perm (Fin n)) =
          restrictO (ψA x : Perm (Fin n)) * ψB b * (restrictO (ψA x : Perm (Fin n)))⁻¹) ∧
    (∀ y : B, (∀ i : Fin n, (i : ℕ) < 4 → ((ψB y : Perm (Fin n)) i : ℕ) < 4) →
      ∃ τ : Perm (Fin n), (∀ i : Fin n, (i : ℕ) < 4 → τ i = i) ∧
        ∀ a : A, ∃ ha : (y : G) * a * (y : G)⁻¹ ∈ A,
          (ψA ⟨_, ha⟩ : Perm (Fin n)) = τ * ψA a * τ⁻¹) ∧
    (∃ β' : Perm (Fin n), (∀ i : Fin n, (i : ℕ) < 4 → β' i = i) ∧
      ∀ y : B, (∀ i : Fin n, (i : ℕ) < 4 → ((ψB y : Perm (Fin n)) i : ℕ) < 4) →
        ∀ a : A, ∃ ha : (y : G) * a * (y : G)⁻¹ ∈ A,
          (ψA ⟨_, ha⟩ : Perm (Fin n)) =
            (β' * restrictO (ψB y : Perm (Fin n)) * β'⁻¹) * ψA a *
              (β' * restrictO (ψB y : Perm (Fin n)) * β'⁻¹)⁻¹) ∧
    (∀ k ∈ Subgroup.centralizer (A : Set G), k ∈ normalizer (B : Set G) ∧
      ∃ π : Perm (Fin n), (∀ i : Fin n, 4 ≤ (i : ℕ) → π i = i) ∧
        ∀ b : B, ∃ hb : k * b * k⁻¹ ∈ B, (ψB ⟨_, hb⟩ : Perm (Fin n)) = π * ψB b * π⁻¹) ∧
    (∀ k ∈ Subgroup.centralizer (B : Set G), k ∈ normalizer (A : Set G) ∧
      ∃ π : Perm (Fin n), (∀ i : Fin n, 4 ≤ (i : ℕ) → π i = i) ∧
        ∀ a : A, ∃ ha : k * a * k⁻¹ ∈ A, (ψA ⟨_, ha⟩ : Perm (Fin n)) = π * ψA a * π⁻¹)

theorem AltPair.exists_altCoords [Finite G] {n : ℕ} {A B : Subgroup G} (hp : AltPair n A B) :
    ∃ ψA ψB, AltCoords n A B ψA ψB := hp.exists_coords

@[expose] def p123 : Perm (Fin 7) := swap 1 2 * swap 2 3

@[expose] def p456 : Perm (Fin 7) := swap 4 5 * swap 5 6

@[expose] def p450 : Perm (Fin 7) := swap 4 5 * swap 5 0

@[expose] def q4523 : Perm (Fin 7) := swap 4 5 * swap 2 3

@[expose] def πx : Perm (Fin 7) := swap 2 3 * (swap 1 4 * swap 2 5 * swap 3 6)

theorem p123_mem : p123 ∈ alternatingGroup (Fin 7) := mem_alternatingGroup.mpr (by decide)
theorem p456_mem : p456 ∈ alternatingGroup (Fin 7) := mem_alternatingGroup.mpr (by decide)
theorem p450_mem : p450 ∈ alternatingGroup (Fin 7) := mem_alternatingGroup.mpr (by decide)
theorem q4523_mem : q4523 ∈ alternatingGroup (Fin 7) := mem_alternatingGroup.mpr (by decide)
theorem πx_mem : πx ∈ alternatingGroup (Fin 7) := mem_alternatingGroup.mpr (by decide)

theorem πx_conj_p123 : πx * p123 * πx⁻¹ = p456 := by decide

theorem q4523_conj : q4523 * p123 * q4523⁻¹ = p123⁻¹ ∧ q4523 * p456 * q4523⁻¹ = p456⁻¹ ∧
    q4523 * p450 * q4523⁻¹ = p450⁻¹ := by decide

@[expose] def a123 : alternatingGroup (Fin 7) := ⟨p123, p123_mem⟩
@[expose] def a456 : alternatingGroup (Fin 7) := ⟨p456, p456_mem⟩
@[expose] def a450 : alternatingGroup (Fin 7) := ⟨p450, p450_mem⟩
@[expose] def a4523 : alternatingGroup (Fin 7) := ⟨q4523, q4523_mem⟩
@[expose] def aπx : alternatingGroup (Fin 7) := ⟨πx, πx_mem⟩

theorem a123_mem_rootAlt : a123 ∈ rootAlt 7 := by
  rw [mem_rootAlt_iff (by norm_num)]
  refine ⟨swap 1 2 * swap 2 3, mem_alternatingGroup.mpr (by decide), ?_⟩
  rw [map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap]
  rfl

end CFSG.ComponentClassification.RankTwoAlt
