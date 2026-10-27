module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedSylow

public section

namespace CFSG.QuasithinUnique.SteinbergBY

open CFSG CFSG.QuasithinUnique.Setup

variable {G : Type*} [Group G]

theorem le_normalizer_of_conj_mem {K Z : Subgroup G} (h : ∀ k ∈ K, ∀ z ∈ Z, k * z * k⁻¹ ∈ Z) :
    K ≤ Subgroup.normalizer (Z : Set G) :=
  le_normalizer_of_map_conj_le fun k hk => by
    rintro _ ⟨z, hz, rfl⟩
    exact h k hk z hz

theorem conj_mem_of_le_normalizer {K Z : Subgroup G} (h : K ≤ Subgroup.normalizer (Z : Set G))
    {k z : G} (hk : k ∈ K) (hz : z ∈ Z) : k * z * k⁻¹ ∈ Z :=
  (Subgroup.mem_normalizer_iff.mp (h hk) z).mp hz

theorem inf_le_normalizer {K Z Z' : Subgroup G} (h : K ≤ Subgroup.normalizer (Z : Set G))
    (h' : K ≤ Subgroup.normalizer (Z' : Set G)) :
    K ≤ Subgroup.normalizer ((Z ⊓ Z' : Subgroup G) : Set G) :=
  le_normalizer_of_conj_mem fun _ hk _ hz =>
    ⟨conj_mem_of_le_normalizer h hk hz.1, conj_mem_of_le_normalizer h' hk hz.2⟩

theorem hasNoTwoQuotient_of_le_oddOrderSubgroup {Z : Subgroup G}
    (h : Z ≤ oddOrderSubgroup Z) : HasNoTwoQuotient Z := by
  have heq : oddOrderSubgroup Z = Z := le_antisymm (oddOrderSubgroup_le Z) h
  have := hasNoTwoQuotient_oddOrderSubgroup Z
  rwa [heq] at this

end CFSG.QuasithinUnique.SteinbergBY
