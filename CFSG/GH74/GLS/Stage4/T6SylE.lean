module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup

theorem t6_exists_normalizer_elt {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {T Q : Subgroup G} (hQ : IsPGroup p ↥Q) (hTQ : T ≤ Q) (hne : T ≠ Q) :
    ∃ n ∈ Q, n ∉ T ∧ ∀ t ∈ T, n * t * n⁻¹ ∈ T := by
  have : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥Q)
  have hlt : T.subgroupOf Q < ⊤ := by
    refine lt_top_iff_ne_top.2 (fun htop => hne (le_antisymm hTQ ?_))
    intro x hx
    have : (⟨x, hx⟩ : ↥Q) ∈ T.subgroupOf Q := by rw [htop]; trivial
    exact this
  obtain ⟨⟨n, hnQ⟩, hn1, hn2⟩ := IsConcreteLE.exists_of_lt (hnc _ hlt)
  refine ⟨n, hnQ, fun hnT => hn2 hnT, fun t ht => ?_⟩
  have := (Subgroup.mem_normalizer_iff.1 hn1 ⟨t, hTQ ht⟩).1 ht
  exact this

theorem t6_exists_invariant_sylow {G : Type} [Group G] [Finite G] {K U : Subgroup G}
    (hU : IsPGroup 2 ↥U) (hK : Odd (Nat.card ↥K)) (hUK : ∀ g ∈ U, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    {p : ℕ} (hp : p.Prime) :
    ∃ Q : Subgroup G, Q ≤ K ∧ IsPGroup p ↥Q ∧ Nat.card ↥Q = p ^ (Nat.card ↥K).factorization p ∧
      ∀ g ∈ U, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUn : U ≤ Subgroup.normalizer (K : Set G) := fun g hg =>
    Subgroup.mem_normalizer_fintype (fun k hk => hUK g hg k hk)
  let inst : MulDistribMulAction ↥U ↥K :=
    { smul := fun t k => ⟨t * k * t⁻¹, (Subgroup.mem_normalizer_iff.mp (hUn t.2) k).mp k.2⟩
      one_smul := fun k => Subtype.ext (by change (1 : G) * k * 1⁻¹ = k; group)
      mul_smul := fun s t k => Subtype.ext (by
        change (s * t : G) * k * (s * t : G)⁻¹ = s * (t * k * (t : G)⁻¹) * (s : G)⁻¹
        group)
      smul_mul := fun t k l => Subtype.ext (by
        change (t : G) * (k * l) * (t : G)⁻¹ = (t * k * (t : G)⁻¹) * (t * l * (t : G)⁻¹)
        group)
      smul_one := fun t => Subtype.ext (by change (t : G) * 1 * (t : G)⁻¹ = 1; group) }
  obtain ⟨S⟩ : Nonempty (Sylow p ↥K) := inferInstance
  have hodd : Odd (Nat.card (Sylow p ↥K)) := by
    rw [Sylow.card_eq_index_normalizer S]
    exact Odd.of_dvd_nat hK (Subgroup.index_dvd_card _)
  have hmod := hU.card_modEq_card_fixedPoints (Sylow p ↥K)
  have hfix : Odd (Nat.card (MulAction.fixedPoints ↥U (Sylow p ↥K))) := by
    have := (Nat.odd_iff.1 hodd)
    rw [Nat.odd_iff]
    have h2 := hmod
    unfold Nat.ModEq at h2
    omega
  obtain ⟨⟨Q₀, hQ₀⟩⟩ : Nonempty (MulAction.fixedPoints ↥U (Sylow p ↥K)) :=
    Finite.card_pos_iff.1 (by obtain ⟨k, hk⟩ := hfix; omega)
  refine ⟨(Q₀ : Subgroup ↥K).map K.subtype, Subgroup.map_subtype_le _, Q₀.isPGroup'.map _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact Sylow.card_eq_multiplicity Q₀
  · rintro g hg _ ⟨k, hk, rfl⟩
    have h1 : (⟨g, hg⟩ : ↥U) • Q₀ = Q₀ := hQ₀ ⟨g, hg⟩
    have h2 : (⟨g, hg⟩ : ↥U) • k ∈ (((⟨g, hg⟩ : ↥U) • Q₀ : Sylow p ↥K) : Subgroup ↥K) := by
      rw [Sylow.pointwise_smul_def]
      exact Subgroup.smul_mem_pointwise_smul k _ (Q₀ : Subgroup ↥K) hk
    rw [h1] at h2
    exact ⟨_, h2, rfl⟩

end CFSG.GH74.GLS.Stage4.Rest.T6
