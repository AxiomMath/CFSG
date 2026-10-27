module

public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2Degree

public section

namespace CFSG.KleinFourBlocks

open CFSG CFSG.Semidihedral.OddFieldSL2Degree CFSG.Semidihedral.NormalInductionConstituent

theorem mem_sup_iff_exists_mul_of_commute {M : Type*} [Group M] {K₁ K₂ : Subgroup M}
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (x : M) :
    x ∈ K₁ ⊔ K₂ ↔ ∃ a ∈ K₁, ∃ b ∈ K₂, a * b = x := by
  have hle : K₁ ≤ Subgroup.normalizer (K₂ : Set M) := fun a ha =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun h hh => (hcomm a ha h hh).symm)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K₁ K₂ hle, Set.mem_mul]
  rfl

theorem exists_surjective_hom_prod_sup {M : Type*} [Group M] (K₁ K₂ : Subgroup M)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) :
    ∃ φ : ↥K₁ × ↥K₂ →* ↥(K₁ ⊔ K₂), Function.Surjective φ := by
  have hc : ∀ (a : ↥K₁) (b : ↥K₂), Commute (Subgroup.inclusion (le_sup_left : K₁ ≤ K₁ ⊔ K₂) a)
      (Subgroup.inclusion (le_sup_right : K₂ ≤ K₁ ⊔ K₂) b) := fun a b =>
    Subtype.ext (by simpa using hcomm a a.2 b b.2)
  refine ⟨(Subgroup.inclusion (le_sup_left : K₁ ≤ K₁ ⊔ K₂)).noncommCoprod
    (Subgroup.inclusion (le_sup_right : K₂ ≤ K₁ ⊔ K₂)) hc, ?_⟩
  rintro ⟨x, hx⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_exists_mul_of_commute hcomm x).1 hx
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext (by rw [MonoidHom.noncommCoprod_apply]; rfl)⟩

theorem exists_blocksIrr_pair_of_central_product {M : Type} [Group M] [Finite M]
    (K₁ K₂ : Subgroup M) (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x)
    {θ : ↥(K₁ ⊔ K₂) → ℂ} (hθ : θ ∈ BlocksIrr ↥(K₁ ⊔ K₂)) :
    ∃ ζ₁ ∈ BlocksIrr ↥K₁, ∃ ζ₂ ∈ BlocksIrr ↥K₂, θ 1 = ζ₁ 1 * ζ₂ 1 := by
  obtain ⟨φ, hφ⟩ := exists_surjective_hom_prod_sup K₁ K₂ hcomm
  have : Fintype ↥K₁ := Fintype.ofFinite _
  have : Fintype ↥K₂ := Fintype.ofFinite _
  have hθφ : θ ∘ φ ∈ BlocksIrr (↥K₁ × ↥K₂) := by
    obtain ⟨V, i₁, i₂, i₃, ρ, hρ, rfl⟩ := hθ
    exact ⟨V, i₁, i₂, i₃, ρ.comp φ,
      CFSG.LyonsUnitaryFour.isIrreducible_comp_surjective φ hφ ρ hρ, rfl⟩
  obtain ⟨⟨α, β⟩, ⟨hα, hβ⟩, hαβ⟩ := CFSG.DirectProduct.outerProductCharacter_surjOn hθφ
  refine ⟨α, hα, β, hβ, ?_⟩
  have h1 := congrFun hαβ 1
  simpa [CFSG.DirectProduct.outerProductCharacter] using h1.symm

theorem exists_restriction_constituent_of_index_le_two {M : Type} [Group M] [Finite M]
    (K : Subgroup M) [K.Normal] (hindex : K.index ≤ 2) {ζ : M → ℂ} (hζ : ζ ∈ BlocksIrr M) :
    ∃ θ ∈ BlocksIrr ↥K, ∃ e : ℕ, e ∣ K.index ∧ ζ 1 = e * θ 1 := by
  have hne : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h12 : K.index = 1 ∨ K.index = 2 := by omega
  rcases h12 with h1 | h2
  · have hK : K = ⊤ := Subgroup.index_eq_one.mp h1
    have hsurj : Function.Surjective K.subtype := fun x => ⟨⟨x, hK ▸ Subgroup.mem_top x⟩, rfl⟩
    obtain ⟨V, i₁, i₂, i₃, ρ, hρ, rfl⟩ := hζ
    refine ⟨ρ.character ∘ K.subtype, ⟨V, i₁, i₂, i₃, ρ.comp K.subtype,
      CFSG.LyonsUnitaryFour.isIrreducible_comp_surjective K.subtype hsurj ρ hρ, rfl⟩, 1,
      by rw [h1], ?_⟩
    simp
  · obtain ⟨θ, hθ, -, -, -, hdeg⟩ := index_two_irreducible_restriction K h2 ζ
      (isIrreducibleCharacterOnGroup_of_mem_blocksIrr hζ)
    refine ⟨θ, mem_blocksIrr_of_isIrreducibleCharacterOnGroup hθ, ?_⟩
    rcases hdeg with h | h
    · refine ⟨1, one_dvd _, ?_⟩
      change ζ 1 = θ 1 at h
      rw [h]
      simp
    · refine ⟨2, h2 ▸ dvd_rfl, ?_⟩
      change ζ 1 = 2 * θ 1 at h
      rw [h]
      simp

theorem iv2_10_5_of_index_le_two
    (M : Type) [Group M] [Finite M] (K₁ K₂ : Subgroup M)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x)
    (hnormal : (K₁ ⊔ K₂).Normal) (hindex : (K₁ ⊔ K₂).index ≤ 2) (ζ : M → ℂ)
    (hζ : ζ ∈ BlocksIrr M) :
    ∃ ζ₁ ∈ BlocksIrr ↥K₁, ∃ ζ₂ ∈ BlocksIrr ↥K₂, ∃ e : ℕ, e ∣ (K₁ ⊔ K₂).index ∧
      ζ 1 = e * (ζ₁ 1 * ζ₂ 1) := by
  obtain ⟨θ, hθ, e, he, hζθ⟩ :=
    exists_restriction_constituent_of_index_le_two (K := K₁ ⊔ K₂) hindex hζ
  obtain ⟨ζ₁, hζ₁, ζ₂, hζ₂, hθ1⟩ := exists_blocksIrr_pair_of_central_product K₁ K₂ hcomm hθ
  exact ⟨ζ₁, hζ₁, ζ₂, hζ₂, e, he, by rw [hζθ, hθ1]⟩

end CFSG.KleinFourBlocks
