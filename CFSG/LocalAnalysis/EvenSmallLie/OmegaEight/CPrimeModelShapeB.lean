module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CPrimeModelLink

public section

namespace CFSG.EvenSmallLie.OmegaEight.CPrimeModel

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Stage1.Model
open CFSG.EvenSmallLie.OmegaEight.Stage0

variable {G : Type} [Group G]

theorem pow_three_mem_of_shapeB {t r : G} {L : Subgroup G} (hK : StepK t L) (hS : ShapeB t L r)
    {x : G} (hx : x ∈ centralizer ({t} : Set G)) : x ^ 3 ∈ L ⊔ zpowers t := by
  have hnorm : ((L ⊔ zpowers t).subgroupOf (centralizer ({t} : Set G))).Normal :=
    ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      exact hK.conj_mem_sup g.2 hn⟩
  have h := Subgroup.pow_index_mem ((L ⊔ zpowers t).subgroupOf (centralizer ({t} : Set G)))
    (⟨x, hx⟩ : centralizer ({t} : Set G))
  have hidx : ((L ⊔ zpowers t).subgroupOf (centralizer ({t} : Set G))).index = 3 :=
    hS.relIndex_eq
  rw [hidx, mem_subgroupOf, Subgroup.coe_pow] at h
  exact h

theorem mem_normalizer_of_sup {t : G} {L X : Subgroup G} (hK : StepK t L) (hXL : X ≤ L) {x : G}
    (hx : x ∈ centralizer ({t} : Set G))
    (hxE : x ∈ normalizer ((X ⊔ zpowers t : Subgroup G) : Set G)) :
    x ∈ normalizer (X : Set G) := by
  have hXeq : X = (X ⊔ zpowers t) ⊓ L := by
    apply le_antisymm (le_inf le_sup_left hXL)
    rintro y ⟨hyE, hyL⟩
    obtain ⟨u, hu, z, hz, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun u hu z hz => by
        rcases hK.mem_zpowers_iff.1 hz with rfl | rfl
        · rw [mul_one, one_mul]
        · exact hK.commute_of_mem (hXL hu)) hyE
    rcases hK.mem_zpowers_iff.1 hz with h | h
    · rwa [h, mul_one]
    · exfalso
      apply hK.not_mem
      rw [h] at hyL
      have e : t = u⁻¹ * (u * t) := by group
      rw [e]
      exact mul_mem (inv_mem (hXL hu)) hyL
  have h := inf_normalizer_le_normalizer_inf ⟨hxE, hK.le_normalizer hx⟩
  rw [← hXeq] at h
  exact h

theorem normalizer_E_shapeB_plus {t r : G} {L : Subgroup G} (hK : StepK t L)
    (hS : ShapeB t L r) (θ : L ≃* OmegaEight.omega1T) :
    ∀ x ∈ centralizer ({t} : Set G),
      x ∈ normalizer ((pull θ (QMm .plus) ⊔ zpowers t : Subgroup G) : Set G) →
        x ∈ L ⊔ zpowers t := fun _ hx hxE =>
  mem_of_normalizer_of_pow_three_plus hK θ hx
    (mem_normalizer_of_sup hK (pull_le_L _) hx hxE) (pow_three_mem_of_shapeB hK hS hx)

end CFSG.EvenSmallLie.OmegaEight.CPrimeModel
