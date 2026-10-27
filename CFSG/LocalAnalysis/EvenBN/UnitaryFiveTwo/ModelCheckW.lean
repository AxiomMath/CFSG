module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckWedge
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer Certificates.U52Yamada

theorem Ssub_eq_sup : Ssub = A₂sub ⊔ X₂sub := by
  refine le_antisymm ?_ (sup_le A₂sub_le_Ssub (le_sup_right.trans (le_sup_left.trans le_sup_left)))
  have hX₃ : X₃sub ≤ A₂sub := le_sup_right.trans le_sup_left
  exact sup_le (sup_le (sup_le (X₁sub_le_A₂sub.trans le_sup_left) le_sup_right)
    (hX₃.trans le_sup_left)) (X₄sub_le_A₂sub.trans le_sup_left)

theorem x₂SU_mul (a c : F4) : x₂SU a * x₂SU c = x₂SU (a + c) :=
  ext_mat (by rw [mat_mul, mat_x₂SU, mat_x₂SU, mat_x₂SU, x₂Mat_mul])

theorem X₂sub_le_closure : X₂sub ≤ closure {x₂SU 1, x₂SU F4.ω} := by
  intro g hg
  obtain ⟨c, hc⟩ := mem_X₂sub.1 hg
  have hg' : g = x₂SU c := ext_mat (by rw [hc, mat_x₂SU])
  have h1 : x₂SU 1 ∈ closure {x₂SU 1, x₂SU F4.ω} := subset_closure (Set.mem_insert _ _)
  have hω : x₂SU F4.ω ∈ closure {x₂SU 1, x₂SU F4.ω} :=
    subset_closure (Set.mem_insert_of_mem _ rfl)
  rw [hg']
  rcases F4_cases c with rfl | rfl | rfl | rfl
  · rw [show x₂SU 0 = 1 from ext_mat (by rw [mat_x₂SU, x₂Mat_zero, mat_one])]
    exact one_mem _
  · exact h1
  · exact hω
  · rw [← x₂SU_mul]
    exact mul_mem hω h1

theorem ZX₄sub_comm {z g : SU52} (hz : z ∈ ZX₄sub) (hg : g ∈ Ssub) : g * z = z * g := by
  obtain ⟨a, b, ha, hzm⟩ := mem_x₄Sub.1 hz
  subst ha
  have hz4 : z ∈ X₄sub := ZX₄sub_le_X₄sub hz
  have hle : Ssub ≤ centralizer ({z} : Set SU52) := by
    refine sup_le (sup_le (sup_le (fun x hx => ?_) (fun x hx => ?_)) (fun x hx => ?_))
      (fun x hx => ?_)
    · obtain ⟨c, d, hxm⟩ := mem_X₁sub.1 hx
      have e := commutator_x₁_x₄ hxm hzm
      rw [mul_zero, x₃Mat_zero, ← mat_one] at e
      have e' := ext_mat e
      refine mem_centralizer_singleton_iff.2 ?_
      calc x * z = x * z * (x⁻¹ * z⁻¹ * x * z)⁻¹ := by rw [e', inv_one, mul_one]
        _ = z * x := by group
    · exact mem_centralizer_singleton_iff.2 (commute_X₂_X₄ hx hz4)
    · exact mem_centralizer_singleton_iff.2 (commute_X₃_X₄ hx hz4)
    · obtain ⟨c, d, hxm⟩ := mem_X₄sub.1 hx
      refine mem_centralizer_singleton_iff.2 (ext_mat ?_)
      rw [mat_mul, mat_mul, hxm, hzm, x₄Mat_mul, x₄Mat_mul]
      simp only [add_zero, zero_add, map_zero, zero_mul, mul_zero]
      rw [add_comm b d]
  exact mem_centralizer_singleton_iff.1 (hle hg)

theorem mem_ZX₄sub_of_comm {f : SU52} (hf : f ∈ Fsub) (h1 : f * x₂SU 1 = x₂SU 1 * f)
    (hω : f * x₂SU F4.ω = x₂SU F4.ω * f) : f ∈ ZX₄sub := by
  obtain ⟨⟨a, b, c⟩, ha, hc, hp⟩ := exists_fMat_of_mem_Fsub hf
  have e1 := congrArg mat h1
  have eω := congrArg mat hω
  rw [mat_mul, mat_mul, hp, mat_x₂SU] at e1 eω
  have key : ∀ a b c : F4, fMat (a, b, c) * x₂Mat 1 = x₂Mat 1 * fMat (a, b, c) →
      fMat (a, b, c) * x₂Mat F4.ω = x₂Mat F4.ω * fMat (a, b, c) → a = 0 ∧ b = 0 := by
    intro a b c
    rw [fMat_eq]
    revert a b c
    decide +kernel
  obtain ⟨rfl, rfl⟩ := key a b c e1 eω
  refine mem_x₄Sub.2 ⟨0, c, rfl, ?_⟩
  rw [hp, fMat_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x₄Mat]

theorem norm_conjX₁ :
    conjX₁ 0 * conjX₁ 1 * conjX₁ F4.ω * conjX₁ (F4.ω + 1) = x₄SU 0 1 zero_one_rel := by
  refine ext_mat ?_
  rw [mat_mul, mat_mul, mat_mul, mat_conjX₁, mat_conjX₁, mat_conjX₁, mat_conjX₁, mat_x₄SU]
  decide +kernel

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
