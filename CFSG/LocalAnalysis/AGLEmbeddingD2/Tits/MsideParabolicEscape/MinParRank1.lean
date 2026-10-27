module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

theorem conj_mem_of_double_coset {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    (A : Subgroup G) (x : G) (hx : ∀ g : G, g ∈ A ∨ ∃ a ∈ A, ∃ b ∈ A, g = a * x * b) :
    ∀ a ∈ A, x⁻¹ * a * x ∈ A := by
  by_cases hxA : x ∈ A
  · intro a ha
    exact A.mul_mem (A.mul_mem (A.inv_mem hxA) ha) hxA
  rcases IsCoatomic.eq_top_or_exists_le_coatom A with hAtop | ⟨M, hM, hAM⟩
  · exact absurd (hAtop ▸ Subgroup.mem_top x) hxA
  have hMn : M.Normal := Subgroup.NormalizerCondition.normal_of_coatom M (Group.normalizerCondition_of_isNilpotent (G := G)) hM
  have hxM : x ∉ M := fun hxM => hM.1 (eq_top_iff.2 fun g _ => by
    rcases hx g with h | ⟨a, ha, b, hb, rfl⟩
    · exact hAM h
    · exact M.mul_mem (M.mul_mem (hAM ha) hxM) (hAM hb))
  have hMA : M ≤ A := fun g hg => by
    rcases hx g with h | ⟨a, ha, b, hb, rfl⟩
    · exact h
    · exfalso
      apply hxM
      have := M.mul_mem (M.mul_mem (M.inv_mem (hAM ha)) hg) (M.inv_mem (hAM hb))
      simpa [mul_assoc] using this
  have hAeq : A = M := le_antisymm hAM hMA
  intro a ha
  rw [hAeq] at ha ⊢
  simpa using hMn.conj_mem a ha x⁻¹

theorem map_le_map_of_two_group_image {K Q : Type*} [Group K] [Finite K] [Group Q]
    (θ : K →* Q) {𝒢 A B H : Subgroup K} {n : K} {M : ℕ} (hM : Odd M)
    (hbr : ∀ g ∈ 𝒢, (∃ h ∈ H, ∃ u ∈ A, g = h * u) ∨
      ∃ u ∈ A, ∃ h ∈ H, ∃ v ∈ A, g = u * n * h * v)
    (hn : n ∈ 𝒢) (hA : A ≤ 𝒢) (hH : H ≤ 𝒢) (hHM : ∀ h ∈ H, h ^ M = 1)
    (hconj : ∀ a ∈ A, n * a * n⁻¹ ∈ B)
    (h2 : ∀ g ∈ 𝒢, ∃ k : ℕ, orderOf (θ g) = 2 ^ k) :
    A.map θ ≤ B.map θ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hθH : ∀ h ∈ H, θ h = 1 := by
    intro h hh
    obtain ⟨k, hk⟩ := h2 h (hH hh)
    have h1 : θ h ^ M = 1 := by rw [← map_pow, hHM h hh, map_one]
    have hcop : Nat.Coprime (2 ^ k) M := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hM)
    have := Nat.eq_one_of_dvd_coprimes hcop (hk ▸ dvd_rfl) (orderOf_dvd_of_pow_eq_one h1)
    exact orderOf_eq_one_iff.1 this
  set G' : Subgroup Q := 𝒢.map θ with hG'
  haveI : Finite ↥G' := Finite.of_surjective
    (fun x : ↥𝒢 => (⟨θ x, Subgroup.mem_map_of_mem θ x.2⟩ : ↥G'))
    (fun ⟨y, g, hg, hgy⟩ => ⟨⟨g, hg⟩, Subtype.ext hgy⟩)
  have hp : IsPGroup 2 ↥G' := by
    refine IsPGroup.iff_orderOf.2 fun ⟨y, hy⟩ => ?_
    obtain ⟨g, hg, rfl⟩ := hy
    obtain ⟨k, hk⟩ := h2 g hg
    exact ⟨k, by rw [← hk, ← Subgroup.orderOf_coe]⟩
  haveI : Group.IsNilpotent ↥G' := hp.isNilpotent
  set A₀ : Subgroup ↥G' := (A.map θ).subgroupOf G' with hA₀
  set x : ↥G' := ⟨θ n, Subgroup.mem_map_of_mem θ hn⟩ with hx0
  have hx : ∀ g : ↥G', g ∈ A₀ ∨ ∃ a ∈ A₀, ∃ b ∈ A₀, g = a * x * b := by
    rintro ⟨y, g₀, hg₀, rfl⟩
    rcases hbr g₀ hg₀ with ⟨h, hh, u, hu, rfl⟩ | ⟨u, hu, h, hh, v, hv, rfl⟩
    · left
      show θ (h * u) ∈ A.map θ
      rw [map_mul, hθH h hh, one_mul]
      exact Subgroup.mem_map_of_mem θ hu
    · right
      refine ⟨⟨θ u, Subgroup.mem_map_of_mem θ (hA hu)⟩, Subgroup.mem_map_of_mem θ hu,
        ⟨θ v, Subgroup.mem_map_of_mem θ (hA hv)⟩, Subgroup.mem_map_of_mem θ hv, ?_⟩
      apply Subtype.ext
      show θ (u * n * h * v) = θ u * θ n * θ v
      rw [map_mul, map_mul, map_mul, hθH h hh, mul_one]
  intro y hy
  obtain ⟨a, ha, rfl⟩ := hy
  have hmem : (⟨θ a, Subgroup.mem_map_of_mem θ (hA ha)⟩ : ↥G') ∈ A₀ :=
    Subgroup.mem_map_of_mem θ ha
  have h3 : (θ n)⁻¹ * θ a * θ n ∈ A.map θ := conj_mem_of_double_coset A₀ x hx _ hmem
  obtain ⟨a₁, ha₁, e⟩ := h3
  refine ⟨n * a₁ * n⁻¹, hconj a₁ ha₁, ?_⟩
  rw [map_mul, map_mul, map_inv, e]
  group

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
