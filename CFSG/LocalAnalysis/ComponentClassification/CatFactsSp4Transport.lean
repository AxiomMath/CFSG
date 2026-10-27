module

public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.ComponentClassification.CatFactsSp4

open Subgroup

variable {G H : Type*} [Group G] [Group H]

theorem map_centralizer_singleton (φ : G ≃* H) (t : G) :
    (centralizer {t}).map φ.toMonoidHom = centralizer {φ t} := by
  ext y
  rw [mem_map, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff] at hx
    change φ x * φ t = φ t * φ x
    rw [← map_mul, ← map_mul, hx]
  · intro hy
    refine ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩
    rw [mem_centralizer_singleton_iff]
    apply φ.injective
    rw [map_mul, map_mul, φ.apply_symm_apply, hy]

theorem isPComponent_map_subgroupOf (p : ℕ) (φ : G ≃* H) {C M : Subgroup G} (hMC : M ≤ C)
    (hM : CFSG.IsPComponent p (M.subgroupOf C)) :
    CFSG.IsPComponent p ((M.map φ.toMonoidHom).subgroupOf (C.map φ.toMonoidHom)) := by
  let ψ : C ≃* C.map φ.toMonoidHom := C.equivMapOfInjective φ.toMonoidHom φ.injective
  have h := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent p ψ hM
  convert h using 1
  ext ⟨x, hx⟩
  rw [mem_subgroupOf, mem_map]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, hMC hm⟩, hm, rfl⟩
  · rintro ⟨⟨c, hc⟩, hcM, hceq⟩
    refine ⟨c, hcM, ?_⟩
    have := congrArg Subtype.val hceq
    exact this

theorem pPrimeCore_eq_bot_of_map (p : ℕ) (φ : G ≃* H) {M : Subgroup G}
    (h : CFSG.pPrimeCore p (M.map φ.toMonoidHom) = ⊥) : CFSG.pPrimeCore p M = ⊥ := by
  have h1 := CFSG.pPrimeCore_map_iso p (M.equivMapOfInjective φ.toMonoidHom φ.injective)
  rw [h] at h1
  rw [eq_bot_iff]
  intro x hx
  have : (M.equivMapOfInjective φ.toMonoidHom φ.injective) x ∈ (⊥ : Subgroup _) := by
    rw [← h1]
    exact mem_map_of_mem _ hx
  rw [mem_bot] at this ⊢
  exact (M.equivMapOfInjective φ.toMonoidHom φ.injective).injective (by rw [this, map_one])

end CFSG.ComponentClassification.CatFactsSp4
