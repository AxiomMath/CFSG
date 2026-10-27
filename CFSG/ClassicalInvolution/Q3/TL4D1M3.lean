module

public import CFSG.ClassicalInvolution.Q3.TL4D1Facts
public import CFSG.ClassicalInvolution.Q3.AE.E64

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE Wr

theorem three_cycle_comm_kList : ∀ c : Equiv.Perm (Fin 4), c * c * c = 1 → c ≠ 1 →
    ∀ a ∈ kList, ∃ k₁ ∈ kList, ∃ k₂ ∈ kList,
      a = (k₁ * ofPerm c * k₁⁻¹ * (ofPerm c)⁻¹) * (k₂ * ofPerm c * k₂⁻¹ * (ofPerm c)⁻¹) := by
  decide +kernel

theorem three_cycle_comm_kStarList : ∀ c : Equiv.Perm (Fin 4), c * c * c = 1 → c ≠ 1 →
    ∀ a ∈ kStarList, ∃ k₁ ∈ kStarList, ∃ k₂ ∈ kStarList,
      a = (k₁ * ofPerm c * k₁⁻¹ * (ofPerm c)⁻¹) * (k₂ * ofPerm c * k₂⁻¹ * (ofPerm c)⁻¹) := by
  decide +kernel

variable {n : ℕ}

theorem memBar_le_closure_of_perm {α : Finset (Fin n)} (h : α.card = 4)
    {σ : Equiv.Perm (Fin n)} (hσα : ∀ x ∈ α, σ x ∈ α) (hσ3 : σ ^ 3 = 1)
    (hσ1 : ∃ x ∈ α, σ x ≠ x) (b : Bool) :
    memBar α h b ≤ Subgroup.closure {x | ∃ k ∈ memBar α h b,
      x = k * mkQ n (ofPerm σ) * k⁻¹ * (mkQ n (ofPerm σ))⁻¹} := by
  classical
  set ι := emb α h with hι
  have hrange : Set.range ι = (α : Set (Fin n)) := range_emb α h
  have hmap : ∀ i, σ (ι i) ∈ Set.range ι := by
    intro i
    rw [hrange]
    have hi : ι i ∈ α := by
      have : ι i ∈ Set.range ι := Set.mem_range_self i
      rw [hrange] at this
      exact this
    exact hσα _ hi
  set c := localPerm ι σ hmap with hc
  have hspec : ∀ i, σ (ι i) = ι (c i) := localPerm_spec ι σ hmap
  have hc3 : c * c * c = 1 := by
    refine Equiv.ext fun i => ι.injective ?_
    have h1 : (σ ^ 3) (ι i) = ι i := by rw [hσ3]; rfl
    rw [pow_three, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hspec, hspec, hspec] at h1
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact h1
  have hc1 : c ≠ 1 := by
    rintro hc1
    obtain ⟨x, hx, hσx⟩ := hσ1
    have hx' : x ∈ Set.range ι := by rw [hrange]; exact hx
    obtain ⟨i, rfl⟩ := hx'
    apply hσx
    rw [hspec, hc1]
    rfl
  set S := {x | ∃ k ∈ memBar α h b, x = k * mkQ n (ofPerm σ) * k⁻¹ * (mkQ n (ofPerm σ))⁻¹}
  have hgen : ∀ k : Wr 4, embed ι k ∈ memAt α h b →
      mkQ n (embed ι (k * ofPerm c * k⁻¹ * (ofPerm c)⁻¹)) ∈ Subgroup.closure S := by
    intro k hk
    refine Subgroup.subset_closure ⟨mkQ n (embed ι k), ⟨embed ι k, hk, rfl⟩, ?_⟩
    have hconj := ofPerm_conj_embed (ι := ι) hspec k⁻¹
    rw [show k * ofPerm c * k⁻¹ * (ofPerm c)⁻¹ = k * (ofPerm c * k⁻¹ * (ofPerm c)⁻¹) by group,
      map_mul (embed ι), ← hconj]
    simp only [map_mul, map_inv]
    group
  rintro _ ⟨a, ha, rfl⟩
  cases b with
  | false =>
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨k₁, hk₁, k₂, hk₂, he⟩ := three_cycle_comm_kStarList c hc3 hc1 a₀ ha₀
    rw [he, map_mul, map_mul]
    exact Subgroup.mul_mem _ (hgen k₁ ⟨k₁, hk₁, rfl⟩) (hgen k₂ ⟨k₂, hk₂, rfl⟩)
  | true =>
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨k₁, hk₁, k₂, hk₂, he⟩ := three_cycle_comm_kList c hc3 hc1 a₀ ha₀
    rw [he, map_mul, map_mul]
    exact Subgroup.mul_mem _ (hgen k₁ ⟨k₁, hk₁, rfl⟩) (hgen k₂ ⟨k₂, hk₂, rfl⟩)

theorem modelThree_of_perm (hn : 5 ≤ n) {𝒜 : Set (Finset (Fin n))}
    {P : Subgroup (Equiv.Perm (Fin n))}
    (hP : ∀ α ∈ 𝒜, ∃ σ ∈ P, Equiv.Perm.sign σ = 1 ∧ (∀ x ∈ α, σ x ∈ α) ∧ σ ^ 3 = 1 ∧
      ∃ x ∈ α, σ x ≠ x) : ModelThree 𝒜 (aeBarOver P) := by
  intro α hα h b
  obtain ⟨σ, hσP, hsg, hσα, hσ3, hσ1⟩ := hP α hα
  obtain ⟨h1, -, h3, -⟩ := yElt_of_perm hn h hσα hσ3 hσ1
  exact ⟨mkQ n (ofPerm σ), ⟨_, ofPerm_mem_aeSubOver hσP hsg, rfl⟩, h1, h3 b,
    memBar_le_closure_of_perm h hσα hσ3 hσ1 b⟩

theorem e64_three : ModelThree e64Sets e64Sub := by
  refine modelThree_of_perm (by norm_num) ?_
  rintro _ ⟨ℓ, hℓ, rfl⟩
  have key : ∀ σ : Equiv.Perm (Fin 7), (∀ s ∈ fanoLines, s.map σ.toEmbedding ∈ fanoLines ∧
      s.map σ⁻¹.toEmbedding ∈ fanoLines) → Equiv.Perm.sign σ = 1 →
      (∀ x ∈ ℓᶜ, σ x ∈ ℓᶜ) → σ ^ 3 = 1 → (∃ x ∈ ℓᶜ, σ x ≠ x) →
      ∃ σ ∈ l32, Equiv.Perm.sign σ = 1 ∧ (∀ x ∈ ℓᶜ, σ x ∈ ℓᶜ) ∧ σ ^ 3 = 1 ∧
        ∃ x ∈ ℓᶜ, σ x ≠ x :=
    fun σ hm hsg hs h3 hmv => ⟨σ, hm, hsg, hs, h3, hmv⟩
  simp only [fanoLines, List.mem_cons, List.mem_nil_iff, or_false] at hℓ
  rcases hℓ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hm, hs, h3, hmv, hsg⟩ := e64Sigma0_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, hs, h3, hmv, hsg⟩ := e64Sigma1_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, hs, h3, hmv, hsg⟩ := e64Sigma2_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, hs, h3, hmv, hsg⟩ := e64Sigma3_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, hs, h3, hmv, hsg⟩ := e64Sigma4_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, hs, h3, hmv, hsg⟩ := e64Sigma5_spec
    exact key _ hm hsg hs h3 hmv
  · obtain ⟨hm, hs, h3, hmv, hsg⟩ := e64Sigma6_spec
    exact key _ hm hsg hs h3 hmv

end CFSG.ClassicalInvolution.Q3.TL4
