module

public import CFSG.GH74.E2.Tools

public section

namespace CFSG.GH74.E2

open Subgroup

theorem isolation {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {t : G} (ht : orderOf t = 2) {S₁ : Subgroup G}
    (hS₁C : S₁ ≤ Cen t) (hS₁2 : IsPGroup 2 S₁) (htS : t ∈ S₁)
    (hmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Cen t → S₁ ≤ P → P = S₁)
    (hcl : ∀ u ∈ S₁, orderOf u = 2 → ∃ c : G, c * t = t * c ∧ c⁻¹ * u * c ∈ S₁ ∧
      ∀ s ∈ S₁, s * (c⁻¹ * u * c) = (c⁻¹ * u * c) * s)
    (hfix : ∀ n ∈ normalizer (S₁ : Set G), ∀ w ∈ S₁, (∀ s ∈ S₁, s * w = w * s) →
      w = n⁻¹ * t * n → w = t) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hP : ∃ P : Subgroup G, IsPGroup 2 P ∧ S₁ ≤ P ∧ P ≠ S₁
  · obtain ⟨n, hn, hne, hmem, hcent⟩ := exists_normalizer_moving hS₁C hmax htS hP
    exact hne (hfix n hn _ hmem hcent rfl)
  · push Not at hP
    obtain ⟨S, hS⟩ := hS₁2.exists_le_sylow
    have hSeq : (S : Subgroup G) = S₁ := hP _ S.isPGroup' hS
    have htS' : t ∈ (S : Subgroup G) := hSeq ▸ htS
    have htc : ∀ s ∈ (S : Subgroup G), s * t = t * s := fun s hs' => by
      rw [hSeq] at hs'
      exact mem_Cen'.1 (hS₁C hs')
    refine tool_Z hs hnab (S := S) ht htS' htc ?_ ?_
    · intro u hu hu2
      rw [hSeq] at hu ⊢
      exact hcl u hu hu2
    · intro n hn w hw hwc hwn
      have hSeqS : (S : Set G) = (S₁ : Set G) := by rw [← hSeq]; rfl
      rw [hSeqS] at hn
      rw [hSeq] at hw hwc
      exact hfix n hn w hw hwc hwn

theorem hfix_of_aut {G : Type} [Group G] {t : G} {S₁ : Subgroup G} (htS : t ∈ S₁)
    (haut : ∀ ψ : MulAut ↥S₁, ψ ⟨t, htS⟩ ∈ Subgroup.center ↥S₁ → ψ ⟨t, htS⟩ = ⟨t, htS⟩) :
    ∀ n ∈ normalizer (S₁ : Set G), ∀ w ∈ S₁, (∀ s ∈ S₁, s * w = w * s) →
      w = n⁻¹ * t * n → w = t := by
  intro n hn w hw hwc hwn
  have hn' : n⁻¹ ∈ normalizer (S₁ : Set G) := inv_mem hn
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MulAut ↥S₁, ψ = S₁.normalizerMonoidHom ⟨n⁻¹, hn'⟩ := ⟨_, rfl⟩
  have hψapp : ∀ x : ↥S₁, ((ψ x : ↥S₁) : G) = n⁻¹ * x * n := fun x => by
    rw [hψ]
    change n⁻¹ * (x : G) * (n⁻¹)⁻¹ = n⁻¹ * x * n
    rw [inv_inv]
  have hψt : ψ ⟨t, htS⟩ = ⟨w, hw⟩ := by
    apply Subtype.ext
    rw [hψapp]
    exact hwn.symm
  have hwcent : (⟨w, hw⟩ : ↥S₁) ∈ Subgroup.center ↥S₁ := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hwc g g.2)
  have := haut ψ (hψt ▸ hwcent)
  rw [hψt] at this
  exact congrArg Subtype.val this

theorem isolation_of_aut {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {t : G} (ht : orderOf t = 2) {S₁ : Subgroup G}
    (hS₁C : S₁ ≤ Cen t) (hS₁2 : IsPGroup 2 S₁) (htS : t ∈ S₁)
    (hmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Cen t → S₁ ≤ P → P = S₁)
    (hcl : ∀ u ∈ S₁, orderOf u = 2 → ∃ c : G, c * t = t * c ∧ c⁻¹ * u * c ∈ S₁ ∧
      ∀ s ∈ S₁, s * (c⁻¹ * u * c) = (c⁻¹ * u * c) * s)
    (haut : ∀ ψ : MulAut ↥S₁, ψ ⟨t, htS⟩ ∈ Subgroup.center ↥S₁ → ψ ⟨t, htS⟩ = ⟨t, htS⟩) :
    False :=
  isolation hs hnab ht hS₁C hS₁2 htS hmax hcl (hfix_of_aut htS haut)

end CFSG.GH74.E2
