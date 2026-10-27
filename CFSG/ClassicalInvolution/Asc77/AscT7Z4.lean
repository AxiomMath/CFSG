module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyClassical
public import CFSG.ClassicalInvolution.Asc77.AscT7Z2

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped commutatorElement MatrixGroups

namespace T7Z

section Lifts

variable {U G : Type} [Group U] [Group G]

theorem exists_commuting_lifts [Finite U] (ψ : U →* G) (hker : ψ.ker ≤ Subgroup.center U)
    (hU : (⊤ : Subgroup U) ≤ ⁅(⊤ : Subgroup U), (⊤ : Subgroup U)⁆) {R₁ R₂ R₃ : Subgroup U}
    (hR₁ : R₁ ≤ ⁅R₁, R₁⁆) (hi₁ : ∀ x ∈ R₁, ψ x = 1 → x = 1)
    (hi₃ : ∀ x ∈ R₃, ψ x = 1 → x = 1) {a b e z t : G} (ha : a ∈ R₁.map ψ) (hb : b ∈ R₂.map ψ)
    (hcomm : Commutes (R₁.map ψ) (R₂.map ψ)) (he : e ∈ ψ.range)
    (hec : ∀ y ∈ ψ.range, e * y = y * e) (hz : a * a = z) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (ht : t ∈ R₃.map ψ) (htab : t = a * b * e) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ∃ c₁ ∈ R₁, ∃ c₂ ∈ R₃, orderOf c₁ = 2 ∧ orderOf c₂ = 2 ∧ ψ c₁ = z ∧ ψ c₂ = t ∧
      c₁ * c₂ = c₂ * c₁ := by
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  obtain ⟨b₀, hb₀, rfl⟩ := hb
  obtain ⟨ε, hε, hψε⟩ := exists_central_lift ψ hker hU he hec
  obtain ⟨c₂, hc₂, hψc₂⟩ := ht
  have hR₁R₂ : Commutes R₁ R₂ := commutes_of_map_commutes ψ hker hR₁ hcomm
  set c₁ : U := a₀ * a₀ with hc₁
  have hc₁R : c₁ ∈ R₁ := R₁.mul_mem ha₀ ha₀
  have hψc₁ : ψ c₁ = z := by rw [hc₁, map_mul, hz]
  have hc₁sq : c₁ * c₁ = 1 := by
    refine hi₁ _ (R₁.mul_mem hc₁R hc₁R) ?_
    rw [map_mul, hψc₁, hz2]
  have hc₁one : c₁ ≠ 1 := by
    intro h
    apply hz1
    rw [← hψc₁, h, map_one]
  have hc₂sq : c₂ * c₂ = 1 := by
    refine hi₃ _ (R₃.mul_mem hc₂ hc₂) ?_
    rw [map_mul, hψc₂, ht2]
  have hc₂one : c₂ ≠ 1 := by
    intro h
    apply ht1
    rw [← hψc₂, h, map_one]
  set τ : U := a₀ * b₀ * ε with hτ
  have hψτ : ψ τ = t := by rw [hτ, map_mul, map_mul, hψε, htab]
  have hκ : c₂⁻¹ * τ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψc₂, hψτ, inv_mul_cancel]
  have hκc : c₂⁻¹ * τ ∈ Subgroup.center U := hker hκ
  have hc₁τ : c₁ * τ = τ * c₁ := by
    have h1 : c₁ * a₀ = a₀ * c₁ := by rw [hc₁]; group
    have h2 : c₁ * b₀ = b₀ * c₁ := hR₁R₂ c₁ hc₁R b₀ hb₀
    have h3 : c₁ * ε = ε * c₁ := Subgroup.mem_center_iff.mp hε c₁
    calc c₁ * τ = c₁ * a₀ * b₀ * ε := by rw [hτ]; group
      _ = a₀ * c₁ * b₀ * ε := by rw [h1]
      _ = a₀ * (c₁ * b₀) * ε := by group
      _ = a₀ * (b₀ * c₁) * ε := by rw [h2]
      _ = a₀ * b₀ * (c₁ * ε) := by group
      _ = a₀ * b₀ * (ε * c₁) := by rw [h3]
      _ = τ * c₁ := by rw [hτ]; group
  have hτeq : τ = c₂ * (c₂⁻¹ * τ) := by group
  refine ⟨c₁, hc₁R, c₂, hc₂, orderOf_eq_prime (by rwa [pow_two]) hc₁one,
    orderOf_eq_prime (by rwa [pow_two]) hc₂one, hψc₁, hψc₂, ?_⟩
  have hκc' : c₁ * (c₂⁻¹ * τ) = (c₂⁻¹ * τ) * c₁ := Subgroup.mem_center_iff.mp hκc c₁
  have key : c₁ * c₂ * (c₂⁻¹ * τ) = c₂ * c₁ * (c₂⁻¹ * τ) := by
    calc c₁ * c₂ * (c₂⁻¹ * τ) = c₁ * τ := by group
      _ = τ * c₁ := hc₁τ
      _ = c₂ * (c₂⁻¹ * τ) * c₁ := by rw [← hτeq]
      _ = c₂ * ((c₂⁻¹ * τ) * c₁) := by group
      _ = c₂ * (c₁ * (c₂⁻¹ * τ)) := by rw [hκc']
      _ = c₂ * c₁ * (c₂⁻¹ * τ) := by group
  exact mul_right_cancel key

end Lifts

section Pair

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem psl_pair_of_lifts (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 4 p f)
    (ψ : (Generic.modelUniv .PSL 4 p f Fact.out).K →* G)
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv .PSL 4 p f Fact.out).K)
    {R₁ R₂ : Subgroup (Generic.modelUniv .PSL 4 p f Fact.out).K}
    (h₁ : R₁ ∈ Generic.fundamentalSubgroups .PSL (Generic.modelUniv .PSL 4 p f Fact.out).D)
    (h₂ : R₂ ∈ Generic.fundamentalSubgroups .PSL (Generic.modelUniv .PSL 4 p f Fact.out).D)
    {c₁ c₂ : (Generic.modelUniv .PSL 4 p f Fact.out).K} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂)
    (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2) (hc : c₁ * c₂ = c₂ * c₁)
    (hne : R₁.map ψ ≠ R₂.map ψ) (hnc : ¬ Commutes (R₁.map ψ) (R₂.map ψ)) :
    (∃ W, LinearBlockStandardPair (GaloisField p f) W R₁ R₂) ∧
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (R₁.map ψ) (R₂.map ψ) := by
  have hl₁ := ModelFacts.fundamentalSubgroups_subset_longest (t := .PSL) (by decide) (by decide)
    _ h₁
  have hl₂ := ModelFacts.fundamentalSubgroups_subset_longest (t := .PSL) (by decide) (by decide)
    _ h₂
  rcases ModelFacts.standardPairDichotomyTypes_psl hadm hp2 hq R₁ hl₁ R₂ hl₂ c₁ c₂ hc₁ hc₂ ho₁
    ho₂ hc with h | h | ⟨-, W, hW⟩ | ⟨hF, -⟩
  · exact absurd (by rw [h]) hne
  · exact absurd (fun x hx y hy => by
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hy
      rw [← map_mul, ← map_mul, h x hx y hy]) hnc
  · exact ⟨⟨W, hW⟩, _, Balance.linearBlockStandardPair_map_of_ker_le_center hW ψ hker⟩
  · exact hF.elim

end Pair

end T7Z

end CFSG.ClassicalInvolution.Asc77
