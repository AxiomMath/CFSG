module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSLc
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagLg

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace CSL

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag DiagL

variable {F : Type} [Field F] {G : Type} [Group G] {N : Subgroup G} [N.Normal]
  (e : ↥N ≃* projectiveSL 4 F)

theorem actP_eq_conj {x : G} (hx : x ∈ N) : actP e x = MulAut.conj (e ⟨x, hx⟩) := by
  ext y
  obtain ⟨z, rfl⟩ := e.surjective y
  rw [actP_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem actP_apply' (g : G) {w : G} (hw : w ∈ N) :
    actP e g (e ⟨w, hw⟩) = e ⟨g * w * g⁻¹, Subgroup.Normal.conj_mem inferInstance w hw g⟩ := by
  rw [actP_apply]
  congr 1

theorem actP_comm_conj {g w : G} (hw : w ∈ N) (hgw : g * w = w * g) :
    actP e g * MulAut.conj (e ⟨w, hw⟩) = MulAut.conj (e ⟨w, hw⟩) * actP e g := by
  have h1 : actP e g (e ⟨w, hw⟩) = e ⟨w, hw⟩ := by
    rw [actP_apply']
    congr 1
    apply Subtype.ext
    change g * w * g⁻¹ = w
    rw [hgw, mul_inv_cancel_right]
  rw [← mul_inv_eq_iff_eq_mul, mul_conj_mul_inv, h1]

omit [N.Normal] in
theorem normalizes_of_mem_normalizer {J : Subgroup G} {c : G} (hcN : c ∈ N)
    (hcJ : c ∈ normalizer (J : Set G)) (y : projectiveSL 4 F) :
    y ∈ (J.subgroupOf N).map e.toMonoidHom ↔
      e ⟨c, hcN⟩ * y * (e ⟨c, hcN⟩)⁻¹ ∈ (J.subgroupOf N).map e.toMonoidHom := by
  obtain ⟨z, rfl⟩ := e.surjective y
  rw [← map_inv, ← map_mul, ← map_mul]
  constructor
  · rintro ⟨w, hw, hwz⟩
    have hwz' : w = z := e.injective hwz
    subst hwz'
    refine ⟨_, ?_, rfl⟩
    simp only [SetLike.mem_coe, mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hw ⊢
    exact (mem_normalizer_iff.mp hcJ _).mp hw
  · rintro ⟨w, hw, hwz⟩
    have hwz' : w = ⟨c, hcN⟩ * z * (⟨c, hcN⟩)⁻¹ := e.injective hwz
    subst hwz'
    refine ⟨z, ?_, rfl⟩
    simp only [SetLike.mem_coe, mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hw ⊢
    exact (mem_normalizer_iff.mp hcJ _).mpr hw

omit [N.Normal] in
theorem mem_normalizer_of_normalizes {J : Subgroup G} (hJN : J ≤ N) {w : G} (hwN : w ∈ N)
    (hw : ∀ y, y ∈ (J.subgroupOf N).map e.toMonoidHom ↔
      e ⟨w, hwN⟩ * y * (e ⟨w, hwN⟩)⁻¹ ∈ (J.subgroupOf N).map e.toMonoidHom) :
    w ∈ normalizer (J : Set G) := by
  rw [mem_normalizer_iff]
  intro j
  have hmem : ∀ z : ↥N, (z : G) ∈ J ↔ e z ∈ (J.subgroupOf N).map e.toMonoidHom := by
    intro z
    constructor
    · intro hz
      exact ⟨z, mem_subgroupOf.mpr hz, rfl⟩
    · rintro ⟨z', hz', hzz⟩
      have : z' = z := e.injective hzz
      rw [← this]
      exact mem_subgroupOf.mp hz'
  constructor
  · intro hj
    have hjN := hJN hj
    have h1 := (hw (e ⟨j, hjN⟩)).1 ((hmem ⟨j, hjN⟩).1 hj)
    rw [← map_inv, ← map_mul, ← map_mul, ← hmem] at h1
    exact h1
  · intro hj
    have hjN : j ∈ N := by
      have h2 : w * j * w⁻¹ ∈ N := hJN hj
      have e2 : j = w⁻¹ * (w * j * w⁻¹) * w := by group
      rw [e2]
      exact mul_mem (mul_mem (inv_mem hwN) h2) hwN
    have h1 : e (⟨w, hwN⟩ * ⟨j, hjN⟩ * (⟨w, hwN⟩)⁻¹) ∈ (J.subgroupOf N).map e.toMonoidHom :=
      (hmem _).1 hj
    rw [map_mul, map_mul, map_inv, ← hw] at h1
    exact (hmem _).2 h1

end CSL

end CFSG.ComponentClassification.CatFactsL4U4
