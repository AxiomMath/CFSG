module

public import CFSG.ClassicalInvolution.Q3.TL4D1Facts

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE

theorem kList_comm_yQ : ∀ a ∈ kList, ∃ k₁ ∈ kList, ∃ k₂ ∈ kList,
    a = (k₁ * yQ * k₁⁻¹ * yQ⁻¹) * (k₂ * yQ * k₂⁻¹ * yQ⁻¹) := by decide +kernel

theorem kStarList_comm_yQ : ∀ a ∈ kStarList, ∃ k₁ ∈ kStarList, ∃ k₂ ∈ kStarList,
    a = (k₁ * yQ * k₁⁻¹ * yQ⁻¹) * (k₂ * yQ * k₂⁻¹ * yQ⁻¹) := by decide +kernel

variable {n : ℕ}

theorem memBar_le_closure_yBar (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    memBar α h b ≤ Subgroup.closure
      {x | ∃ k ∈ memBar α h b, x = k * yBar α h * k⁻¹ * (yBar α h)⁻¹} := by
  set ι := emb α h with hι
  set S := {x | ∃ k ∈ memBar α h b, x = k * yBar α h * k⁻¹ * (yBar α h)⁻¹} with hS
  have hy : yBar α h = mkQ n (embed ι yQ) := rfl
  have hgen : ∀ k : Wr 4, embed ι k ∈ memAt α h b →
      mkQ n (embed ι (k * yQ * k⁻¹ * yQ⁻¹)) ∈ Subgroup.closure S := by
    intro k hk
    refine Subgroup.subset_closure ⟨mkQ n (embed ι k), ⟨embed ι k, hk, rfl⟩, ?_⟩
    rw [hy]
    simp only [map_mul, map_inv]
  rintro _ ⟨a, ha, rfl⟩
  cases b with
  | false =>
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨k₁, hk₁, k₂, hk₂, he⟩ := kStarList_comm_yQ a₀ ha₀
    rw [he, map_mul, map_mul]
    exact Subgroup.mul_mem _ (hgen k₁ ⟨k₁, hk₁, rfl⟩) (hgen k₂ ⟨k₂, hk₂, rfl⟩)
  | true =>
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨k₁, hk₁, k₂, hk₂, he⟩ := kList_comm_yQ a₀ ha₀
    rw [he, map_mul, map_mul]
    exact Subgroup.mul_mem _ (hgen k₁ ⟨k₁, hk₁, rfl⟩) (hgen k₂ ⟨k₂, hk₂, rfl⟩)

theorem aeModelThree (m : ℕ) : ModelThree (Set.univ : Set (Finset (Fin m))) (aeModel m) :=
  fun α _ h b => ⟨yBar α h, yBar_mem α h, yBar_pow_three α h, yBar_conj_mem_memBar α h b,
    memBar_le_closure_yBar α h b⟩

end CFSG.ClassicalInvolution.Q3.TL4
