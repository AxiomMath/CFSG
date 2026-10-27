module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Comm

variable {G : Type} [Group G]

theorem commutator_sup_le_of_comm {A N : Subgroup G}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAN : A ≤ Subgroup.normalizer (N : Set G)) :
    ⁅A ⊔ N, A ⊔ N⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A N hAN] at hx hy
  obtain ⟨a₁, ha₁, n₁, hn₁, rfl⟩ := hx
  obtain ⟨a₂, ha₂, n₂, hn₂, rfl⟩ := hy
  have hc : a₁ * a₂ * a₁⁻¹ * a₂⁻¹ = 1 := by rw [hA a₁ ha₁ a₂ ha₂]; group
  have key : ⁅a₁ * n₁, a₂ * n₂⁆ = (a₁ * n₁ * a₁⁻¹) * ((a₁ * a₂) * (n₂ * n₁⁻¹) * (a₁ * a₂)⁻¹) *
      ((a₁ * a₂ * a₁⁻¹) * n₂⁻¹ * (a₁ * a₂ * a₁⁻¹)⁻¹) * (a₁ * a₂ * a₁⁻¹ * a₂⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [key, hc, mul_one]
  have hconj : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N := fun a ha n hn =>
    (Subgroup.mem_normalizer_iff.mp (hAN ha) n).mp hn
  refine N.mul_mem (N.mul_mem (hconj a₁ ha₁ n₁ hn₁) (hconj _ (A.mul_mem ha₁ ha₂) _
    (N.mul_mem hn₂ (N.inv_mem hn₁)))) (hconj _ (A.mul_mem (A.mul_mem ha₁ ha₂) (A.inv_mem ha₁))
    _ (N.inv_mem hn₂))

end Comm

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Count

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_barM_le (M X : Subgroup G) :
    ⁅barM M X, barM M X⁆ ≤ barM M ⁅X, X⁆ := by
  rw [Subgroup.commutator_le]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  refine ⟨⁅x, y⁆, Subgroup.mem_subgroupOf.mpr ?_, by simp [commutatorElement_def]⟩
  simpa [commutatorElement_def] using
    Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hx)
      (Subgroup.mem_subgroupOf.mp hy)

theorem pow_le_of_dvd_card {T : Subgroup G} {b : ℕ}
    (hT : ∀ B : Subgroup G, B ≤ T → IsPGroup 3 B → Nat.card B ≤ b) {a : ℕ}
    (ha : 3 ^ a ∣ Nat.card T) : 3 ^ a ≤ b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K', hK'⟩ := Sylow.exists_subgroup_card_pow_prime 3 ha
  have hB := hT (K'.map T.subtype) (Subgroup.map_subtype_le _)
    ((IsPGroup.of_card hK').map _)
  rwa [Subgroup.card_map_of_injective T.subtype_injective, hK'] at hB

end Count

end CFSG.AGLEmbedding
