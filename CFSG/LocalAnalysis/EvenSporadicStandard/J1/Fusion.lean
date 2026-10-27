module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion

public section

namespace CFSG.EvenSporadicStandard.J1Std

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem eq_of_inf_normalizer_le {P S : Subgroup G} (hP : IsPGroup 2 P)
    (hSP : S ≤ P) (h : ∀ x ∈ P, x ∈ normalizer (S : Set G) → x ∈ S) : S = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥P)
  have hnorm : normalizer ((S.subgroupOf P : Subgroup ↥P) : Set ↥P) = S.subgroupOf P := by
    refine le_antisymm (fun x hx => ?_) (le_normalizer)
    rw [mem_subgroupOf]
    refine h x x.2 (mem_normalizer_iff.2 fun s => ?_)
    constructor
    · intro hs
      have := (mem_normalizer_iff.1 hx ⟨s, hSP hs⟩).1 (by rw [mem_subgroupOf]; exact hs)
      rwa [mem_subgroupOf] at this
    · intro hs
      have hsP : s ∈ P := by
        have := hSP hs
        have h2 : x⁻¹ * (x * s * x⁻¹) * x ∈ P := P.mul_mem (P.mul_mem (P.inv_mem x.2) this) x.2
        simpa [mul_assoc] using h2
      have := (mem_normalizer_iff.1 hx ⟨s, hsP⟩).2 (by rw [mem_subgroupOf]; exact hs)
      rwa [mem_subgroupOf] at this
  have htop := (normalizerCondition_iff_only_full_group_self_normalizing.1 hnc) _ hnorm
  refine le_antisymm hSP (fun x hx => ?_)
  have : (⟨x, hx⟩ : ↥P) ∈ S.subgroupOf P := by rw [htop]; exact mem_top _
  exact this

theorem not_two_dvd_index_of_invariant {S : Subgroup G} (hS : IsPGroup 2 S) {z : G}
    (hmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({z} : Set G) →
      centralizer ({z} : Set G) ⊓ S ≤ P → P ≤ S)
    (hinv : ∀ n ∈ normalizer (S : Set G), ∃ s ∈ S, n * z * n⁻¹ = s * z * s⁻¹) :
    ¬ 2 ∣ S.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h2
  obtain ⟨T, hST⟩ := hS.exists_le_sylow
  have hne : S ≠ (T : Subgroup G) := fun heq => T.not_dvd_index (heq ▸ h2)
  obtain ⟨τ, hτT, hτN, hτS⟩ : ∃ τ ∈ (T : Subgroup G), τ ∈ normalizer (S : Set G) ∧ τ ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hne (eq_of_inf_normalizer_le T.isPGroup' hST hcon)
  obtain ⟨s, hs, hsτ⟩ := hinv τ hτN
  have huC : s⁻¹ * τ ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc s⁻¹ * τ * z = s⁻¹ * (τ * z * τ⁻¹) * τ := by group
      _ = s⁻¹ * (s * z * s⁻¹) * τ := by rw [hsτ]
      _ = z * (s⁻¹ * τ) := by group
  have huT : s⁻¹ * τ ∈ (T : Subgroup G) := mul_mem (inv_mem (hST hs)) hτT
  have hP : IsPGroup 2 (centralizer ({z} : Set G) ⊓ (T : Subgroup G) : Subgroup G) :=
    T.isPGroup'.to_inf_right
  have huS := hmax _ hP inf_le_left (inf_le_inf_left _ hST) ⟨huC, huT⟩
  apply hτS
  have h3 : τ = s * (s⁻¹ * τ) := by group
  rw [h3]
  exact mul_mem hs huS

theorem two_dvd_index_of_avoid [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {S U : Subgroup G} (hS : IsPGroup 2 S) (hUS : U ≤ S) (hU : U.relIndex S = 2) {z : G}
    (hzS : z ∈ S) (hzU : z ∉ U) (hz2 : orderOf z = 2) (havoid : ∀ g : G, g⁻¹ * z * g ∉ U) :
    2 ∣ S.index := by
  by_contra h
  obtain ⟨g, hg⟩ := CFSG.EvenSporadicStandard.exists_conj_mem_complement hnonab hS h hUS hU hzS
    hzU hz2
  exact havoid g hg

end CFSG.EvenSporadicStandard.J1Std
