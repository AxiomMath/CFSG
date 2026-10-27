module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeData
public import CFSG.HardMathSupport.Cooperstein.StructureLie.McLaughlinShape

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open Module CFSG.ComponentClassification.OutcomeLocal
open scoped commutatorElement

theorem nonempty_mulEquiv_alternating_of_commutator_range {m : ℕ} (hm : 5 ≤ m) {W' : Type*}
    [AddCommGroup W'] [Module (ZMod 2) W']
    (ρ : Equiv.Perm (Fin m) →* LinearMap.GeneralLinearGroup (ZMod 2) W')
    (hne : ⁅ρ.range, ρ.range⁆ ≠ ⊥) :
    Nonempty (↥⁅ρ.range, ρ.range⁆ ≃* alternatingGroup (Fin m)) := by
  have h5 : 5 ≤ Nat.card (Fin m) := by simpa using hm
  have hcomm : ⁅ρ.range, ρ.range⁆ = (alternatingGroup (Fin m)).map ρ := by
    have h : ⁅(⊤ : Subgroup (Equiv.Perm (Fin m))), ⊤⁆ = alternatingGroup (Fin m) := by
      rw [← _root_.commutator_def]
      exact alternatingGroup.commutator_perm_eq h5
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, h]
  let ψ : alternatingGroup (Fin m) →* LinearMap.GeneralLinearGroup (ZMod 2) W' :=
    ρ.comp (alternatingGroup (Fin m)).subtype
  have hψr : ψ.range = (alternatingGroup (Fin m)).map ρ := by
    simp only [ψ, MonoidHom.range_comp, Subgroup.range_subtype]
  have : IsSimpleGroup (alternatingGroup (Fin m)) := alternatingGroup.isSimpleGroup h5
  have hinj : Function.Injective ψ := by
    rcases ψ.normal_ker.eq_bot_or_eq_top with hb | ht
    · exact (MonoidHom.ker_eq_bot_iff ψ).mp hb
    · exfalso
      apply hne
      rw [hcomm, ← hψr]
      rw [eq_bot_iff]
      rintro _ ⟨a, rfl⟩
      have : a ∈ ψ.ker := by rw [ht]; trivial
      rw [Subgroup.mem_bot]
      exact this
  exact ⟨(MulEquiv.subgroupCongr (hcomm.trans hψr.symm)).trans
    (MonoidHom.ofInjective hinj).symm⟩

theorem nonempty_mulEquiv_alternating_of_conj_range {m : ℕ} (hm : 5 ≤ m) {W W' : Type*}
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup W'] [Module (ZMod 2) W']
    (ρ : Equiv.Perm (Fin m) →* LinearMap.GeneralLinearGroup (ZMod 2) W')
    (β : W ≃ₗ[ZMod 2] W') (H L : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W))
    (hH : H.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom = ρ.range)
    (hL : L = ⁅H, H⁆) (hL1 : L ≠ ⊥) : Nonempty (↥L ≃* alternatingGroup (Fin m)) := by
  set e := LinearMap.GeneralLinearGroup.congrLinearEquiv β with he
  have hmap : L.map e.toMonoidHom = ⁅ρ.range, ρ.range⁆ := by
    rw [hL, Subgroup.map_commutator, hH]
  have hne : ⁅ρ.range, ρ.range⁆ ≠ ⊥ := by
    rw [← hmap]
    intro h
    exact hL1 ((Subgroup.map_eq_bot_iff_of_injective L e.injective).mp h)
  obtain ⟨φ⟩ := nonempty_mulEquiv_alternating_of_commutator_range hm ρ hne
  exact ⟨((Subgroup.equivMapOfInjective L e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hmap)).trans φ⟩

theorem shapeOut_of_perfect_index_two {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (hn : 1 ≤ Module.finrank (ZMod 2) W)
    (H L : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W))
    (hgen : ∃ S : Set (LinearMap.GeneralLinearGroup (ZMod 2) W),
      (∀ t ∈ S, IsF2Transvection t) ∧ H = Subgroup.closure S)
    (hirr : ∀ U : Submodule (ZMod 2) W,
      (∀ g ∈ H, ∀ u ∈ U, (g : W →ₗ[ZMod 2] W) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hLH : L ≤ H) (hidx : L.relIndex H = 2) (hperf : ⁅L, L⁆ = L) (hL1 : L ≠ ⊥) :
    ShapeOut ↥L := by
  have h3 : 3 ≤ finrank (ZMod 2) W := by
    by_contra hlt
    exact hL1 (eq_bot_of_isPerfect_of_finrank_le_two (by omega) L hperf)
  obtain ⟨hLeq, hcases⟩ := shape_of_perfect_index_two hn H L hgen hirr hLH hidx hperf hL1
  rcases hcases with ⟨h4, f, hnd, halt, hH⟩ | ⟨Q, hQ, hH⟩ | ⟨he, hsym⟩
  · refine Or.inr (Or.inl ⟨W, inferInstance, inferInstance, inferInstance, f, h4, hnd, halt,
      ⟨MulEquiv.subgroupCongr ?_⟩⟩)
    rw [hLeq, hH]
  · refine Or.inl ⟨W, inferInstance, inferInstance, inferInstance, Q, hQ,
      ⟨MulEquiv.subgroupCongr ?_⟩⟩
    rw [hLeq, hH]
    rfl
  · obtain ⟨k, hk⟩ := he
    refine Or.inr (Or.inr ?_)
    rcases hsym with ⟨β, hβ⟩ | ⟨β, hβ⟩
    · refine ⟨finrank (ZMod 2) W + 1, by omega, ?_⟩
      exact nonempty_mulEquiv_alternating_of_conj_range (by omega) _ β H L hβ hLeq hL1
    · refine ⟨finrank (ZMod 2) W + 2, by omega, ?_⟩
      exact nonempty_mulEquiv_alternating_of_conj_range (by omega) _ β H L hβ hLeq hL1

end CFSG.HardMathSupport.Cooperstein.StructureLie
