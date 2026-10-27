module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Set

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G]

theorem fz410_exists_u {T : Subgroup G} (hT : IsPGroup 2 T) (hns : ¬ FzSylow T) :
    ∃ u ∈ normalizer (T : Set G), u ∉ T ∧ IsPGroup 2 ↥(T ⊔ zpowers u) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hTS⟩ := hT.exists_le_sylow
  have hSp : IsPGroup 2 (S : Subgroup G) := S.isPGroup'
  have hlt : T < (S : Subgroup G) := by
    refine lt_of_le_of_ne hTS (fun h => hns ⟨hT, ?_⟩)
    rw [h]
    exact S.not_dvd_index
  haveI : Group.IsNilpotent ↥(S : Subgroup G) := hSp.isNilpotent
  have hlt' : T.subgroupOf (S : Subgroup G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    rw [Subgroup.subgroupOf_eq_top] at h
    exact not_le_of_gt hlt h
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := ↥(S : Subgroup G)) _ hlt'
  obtain ⟨x, hxN, hxT⟩ := SetLike.exists_of_lt hgrow
  have hxN' : (x : G) ∈ normalizer (T : Set G) := by
    have := hxN
    rw [← Subgroup.subgroupOf_normalizer_eq hlt.le] at this
    exact this
  have hxT' : (x : G) ∉ T := hxT
  exact ⟨x, hxN', hxT', hSp.to_le (sup_le hlt.le (Subgroup.zpowers_le.2 x.2))⟩

namespace Fz410Set

variable {t : G} {L S T : Subgroup G}
  {x₁ x₂ lam rho tau s : G} {Z E W Q R P : Subgroup G}
  (D : Fz410Set t L S T x₁ x₂ lam rho tau s Z E W Q R P)

include D

theorem u_notin_N2 {u : G} (hu : u ∈ normalizer (T : Set G)) (huT : u ∉ T)
    (hp : IsPGroup 2 ↥(T ⊔ zpowers u)) : u ∉ fzN2 t x₁ x₂ := by
  intro huN
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTV : T ≤ T ⊔ zpowers u := le_sup_left
  have hVN : T ⊔ zpowers u ≤ fzN2 t x₁ x₂ :=
    sup_le D.isT2.le_N2 (Subgroup.zpowers_le.2 huN)
  have hdvd : T.relIndex (T ⊔ zpowers u) ∣ T.relIndex (fzN2 t x₁ x₂) :=
    ⟨_, (relIndex_mul_relIndex T (T ⊔ zpowers u) _ hTV hVN).symm⟩
  obtain ⟨n, hn⟩ := hp.index (T.subgroupOf (T ⊔ zpowers u))
  have hn' : T.relIndex (T ⊔ zpowers u) = 2 ^ n := hn
  have hn0 : n = 0 := by
    by_contra h
    exact D.isT2.odd_relIndex ((hn' ▸ dvd_pow_self 2 h).trans hdvd)
  rw [hn0, pow_zero, relIndex_eq_one] at hn'
  exact huT (hn' (Subgroup.mem_sup_right (Subgroup.mem_zpowers u)))

theorem u_mem_N3 {u : G} (hu : u ∈ normalizer (T : Set G)) : u ∈ normalizer (R : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hu' : u⁻¹ ∈ normalizer (T : Set G) := Subgroup.inv_mem _ hu
  constructor
  · exact D.facts.charR u hu h
  · intro hh
    have := D.facts.charR u⁻¹ hu' _ hh
    simpa [mul_assoc] using this

end Fz410Set

end CFSG.OddStandard.SmallF3.FritzII
