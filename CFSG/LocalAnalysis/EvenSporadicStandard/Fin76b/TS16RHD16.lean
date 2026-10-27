module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem klein_dih8_r4_sq : (DihedralGroup.r 4 : DihedralGroup 8) * DihedralGroup.r 4 = 1 := by
  decide

theorem klein_dih8_sr0_sq : (DihedralGroup.sr 0 : DihedralGroup 8) * DihedralGroup.sr 0 = 1 := by
  decide

theorem klein_dih8_r4_ne_one : (DihedralGroup.r 4 : DihedralGroup 8) ≠ 1 := by
  decide

theorem klein_dih8_sr0_ne_one : (DihedralGroup.sr 0 : DihedralGroup 8) ≠ 1 := by
  decide

theorem klein_dih8_r4_ne_sr0 : (DihedralGroup.r 4 : DihedralGroup 8) ≠ DihedralGroup.sr 0 := by
  decide

theorem klein_dih8_comm :
    (DihedralGroup.r 4 : DihedralGroup 8) * DihedralGroup.sr 0 =
      DihedralGroup.sr 0 * DihedralGroup.r 4 := by
  decide

theorem klein_dih8_sr4 :
    (DihedralGroup.sr 4 : DihedralGroup 8) = DihedralGroup.r 4 * DihedralGroup.sr 0 := by
  decide

theorem klein_dih8_central :
    ∀ x : DihedralGroup 8, x * DihedralGroup.r 4 = DihedralGroup.r 4 * x := by
  decide

theorem klein_dih8_centralizer :
    ∀ x : DihedralGroup 8, x * DihedralGroup.sr 0 = DihedralGroup.sr 0 * x →
      x * DihedralGroup.r 4 = DihedralGroup.r 4 * x →
        x = 1 ∨ x = DihedralGroup.r 4 ∨ x = DihedralGroup.sr 0 ∨ x = DihedralGroup.sr 4 := by
  decide

theorem klein_dih8_closure :
    (Subgroup.closure ({DihedralGroup.r 4, DihedralGroup.sr 0} : Set (DihedralGroup 8)) :
      Set (DihedralGroup 8)) = {1, DihedralGroup.r 4, DihedralGroup.sr 0, DihedralGroup.sr 4} := by
  have hmul : ∀ a b : DihedralGroup 8,
      (a = 1 ∨ a = DihedralGroup.r 4 ∨ a = DihedralGroup.sr 0 ∨ a = DihedralGroup.sr 4) →
      (b = 1 ∨ b = DihedralGroup.r 4 ∨ b = DihedralGroup.sr 0 ∨ b = DihedralGroup.sr 4) →
      (a * b = 1 ∨ a * b = DihedralGroup.r 4 ∨ a * b = DihedralGroup.sr 0 ∨
        a * b = DihedralGroup.sr 4) := by
    decide
  have hinv : ∀ a : DihedralGroup 8,
      (a = 1 ∨ a = DihedralGroup.r 4 ∨ a = DihedralGroup.sr 0 ∨ a = DihedralGroup.sr 4) →
      (a⁻¹ = 1 ∨ a⁻¹ = DihedralGroup.r 4 ∨ a⁻¹ = DihedralGroup.sr 0 ∨
        a⁻¹ = DihedralGroup.sr 4) := by
    decide
  ext x
  simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hx
    exact Subgroup.closure_induction
      (p := fun g _ => g = 1 ∨ g = DihedralGroup.r 4 ∨ g = DihedralGroup.sr 0 ∨
        g = DihedralGroup.sr 4)
      (fun y hy => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl <;> simp)
      (Or.inl rfl) (fun a b _ _ ha hb => hmul a b ha hb) (fun a _ ha => hinv a ha) hx
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact subset_closure (Set.mem_insert _ _)
    · exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · rw [klein_dih8_sr4]
      exact mul_mem (subset_closure (Set.mem_insert _ _))
        (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem klein_dih8_card :
    Nat.card ↥(Subgroup.closure ({DihedralGroup.r 4, DihedralGroup.sr 0} :
      Set (DihedralGroup 8))) = 4 := by
  have h1 : (1 : DihedralGroup 8) ∉
      ({DihedralGroup.r 4, DihedralGroup.sr 0, DihedralGroup.sr 4} :
        Set (DihedralGroup 8)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    decide
  have h2 : (DihedralGroup.r 4 : DihedralGroup 8) ∉
      ({DihedralGroup.sr 0, DihedralGroup.sr 4} : Set (DihedralGroup 8)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    decide
  have h3 : (DihedralGroup.sr 0 : DihedralGroup 8) ≠ DihedralGroup.sr 4 := by
    decide
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, klein_dih8_closure,
    Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_pair h3]

theorem exists_klein_selfcentralizing {G : Type} [Group G] {V0 : Subgroup G}
    (e : ↥V0 ≃* DihedralGroup 8) :
    ∃ c d : G, c ∈ V0 ∧ d ∈ V0 ∧ c * c = 1 ∧ d * d = 1 ∧ c ≠ 1 ∧ d ≠ 1 ∧ c ≠ d ∧
      c * d = d * c ∧ (∀ v ∈ V0, v * c = c * v) ∧
      (∀ v ∈ V0, v * c = c * v → v * d = d * v → v ∈ Subgroup.closure ({c, d} : Set G)) ∧
      Nat.card ↥(Subgroup.closure ({c, d} : Set G)) = 4 := by
  let f : DihedralGroup 8 →* G := V0.subtype.comp e.symm.toMonoidHom
  have hinj : Function.Injective f := V0.subtype_injective.comp e.symm.injective
  have hmem : ∀ x, f x ∈ V0 := fun x => (e.symm x).2
  have hsurj : ∀ v ∈ V0, ∃ x, f x = v := fun v hv =>
    ⟨e ⟨v, hv⟩, by
      show ((e.symm (e ⟨v, hv⟩) : V0) : G) = v
      rw [MulEquiv.symm_apply_apply]⟩
  refine ⟨f (DihedralGroup.r 4), f (DihedralGroup.sr 0), hmem _, hmem _,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← f.map_mul, klein_dih8_r4_sq, f.map_one]
  · rw [← f.map_mul, klein_dih8_sr0_sq, f.map_one]
  · exact fun h => klein_dih8_r4_ne_one (hinj (h.trans f.map_one.symm))
  · exact fun h => klein_dih8_sr0_ne_one (hinj (h.trans f.map_one.symm))
  · exact fun h => klein_dih8_r4_ne_sr0 (hinj h)
  · rw [← f.map_mul, ← f.map_mul, klein_dih8_comm]
  · intro v hv
    obtain ⟨x, rfl⟩ := hsurj v hv
    rw [← f.map_mul, ← f.map_mul, klein_dih8_central x]
  · intro v hv hvc hvd
    obtain ⟨x, rfl⟩ := hsurj v hv
    have hx1 : x * DihedralGroup.r 4 = DihedralGroup.r 4 * x := by
      apply hinj
      rw [f.map_mul, f.map_mul]
      exact hvc
    have hx2 : x * DihedralGroup.sr 0 = DihedralGroup.sr 0 * x := by
      apply hinj
      rw [f.map_mul, f.map_mul]
      exact hvd
    rcases klein_dih8_centralizer x hx2 hx1 with rfl | rfl | rfl | rfl
    · rw [f.map_one]
      exact one_mem _
    · exact subset_closure (Set.mem_insert _ _)
    · exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · rw [klein_dih8_sr4, f.map_mul]
      exact mul_mem (subset_closure (Set.mem_insert _ _))
        (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  · have hcl : closure ({f (DihedralGroup.r 4), f (DihedralGroup.sr 0)} : Set G) =
        (closure ({DihedralGroup.r 4, DihedralGroup.sr 0} : Set (DihedralGroup 8))).map f := by
      rw [MonoidHom.map_closure, Set.image_pair]
    rw [hcl, Subgroup.card_map_of_injective hinj, klein_dih8_card]

end CFSG.EvenSporadicStandard.Fin76b
