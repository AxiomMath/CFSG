module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CI3A6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec5m1t_hom_trivial {K E : Type} [Group K] [Finite K] [Group E] (hK : IsSL23Mod K)
    (hE : ∀ e : E, e * e = 1) (f : K →* E) (k : K) : f k = 1 := by
  obtain ⟨e⟩ := hK
  have hcore : CFSG.pPrimeCore 2 K = CFSG.oddCore K := by
    rw [CFSG.pPrimeCore_eq_piCore (G := K) 2, CFSG.oddCore_eq_piCore (G := K)]
  exact CFSG.ComponentClassification.GSThmB.Eight2.Three.eq_one_of_two_elements
    ((QuotientGroup.quotientMulEquivOfEq hcore).trans e) f
    (fun n => ⟨1, by rw [pow_one, pow_two]; exact hE (f n)⟩) k

theorem sec5m1t_index_two {M : Type} [Group M] {Y N : Subgroup M} {π : M}
    (hπc : ∀ g : M, π * g = g * π) (hπY : π ∈ Y) (hπN : π ∉ N)
    (hcov : ∀ g ∈ Y, g ∈ N ∨ π * g ∈ N) : (N.subgroupOf Y).index = 2 := by
  refine Subgroup.index_eq_two_iff.mpr ⟨⟨π, hπY⟩, fun b => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  change Xor' ((b : M) * π ∈ N) ((b : M) ∈ N)
  by_cases hb : (b : M) ∈ N
  · refine Or.inr ⟨hb, fun hbπ => hπN ?_⟩
    have h := N.mul_mem (N.inv_mem hb) hbπ
    simpa using h
  · refine Or.inl ⟨?_, hb⟩
    rcases hcov b b.2 with h | h
    · exact absurd h hb
    · rw [← hπc]
      exact h

theorem sec5m1t_map_le_of_cover {M : Type} [Group M] {Y N : Subgroup M} {π : M}
    (hπc : ∀ g : M, π * g = g * π) (hπY : π ∈ Y) (hπN : π ∉ N)
    (hcov : ∀ g ∈ Y, g ∈ N ∨ π * g ∈ N) {K : Type} [Group K] [Finite K] (hK : IsSL23Mod K)
    (f : K →* M) (hf : ∀ k, f k ∈ Y) (k : K) : f k ∈ N := by
  have hidx := sec5m1t_index_two hπc hπY hπN hcov
  haveI : (N.subgroupOf Y).Normal := Subgroup.normal_of_index_eq_two hidx
  let F : K →* ↥Y ⧸ N.subgroupOf Y :=
    (QuotientGroup.mk' (N.subgroupOf Y)).comp (f.codRestrict Y hf)
  have hE2 : ∀ x : ↥Y ⧸ N.subgroupOf Y, x * x = 1 := by
    intro x
    have h := pow_card_eq_one' (x := x)
    have hc : Nat.card (↥Y ⧸ N.subgroupOf Y) = 2 := hidx
    rw [hc, pow_two] at h
    exact h
  have h1 : F k = 1 := sec5m1t_hom_trivial hK hE2 F k
  have h2 : (⟨f k, hf k⟩ : ↥Y) ∈ N.subgroupOf Y :=
    (QuotientGroup.eq_one_iff (N := N.subgroupOf Y) _).mp h1
  exact h2

end CFSG.OddStandard.SmallF3.Omega
