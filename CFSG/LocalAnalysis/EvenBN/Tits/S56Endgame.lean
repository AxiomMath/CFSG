module

public import CFSG.LocalAnalysis.EvenBN.Common.Endgames

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.S56

open Subgroup CFSG.ABGLocalTools

theorem s56_forall_conj_notMem {G : Type*} [Group G] (S S₀ : Subgroup G) (t : G)
    (hfus : ∀ g : G, g⁻¹ * t * g ∈ S → ∃ s ∈ S, g⁻¹ * t * g = s⁻¹ * t * s)
    (hS₀ : S₀ ≤ S) (hidx : S₀.relIndex S = 2) (htS₀ : t ∉ S₀) :
    ∀ g : G, g⁻¹ * t * g ∉ S₀ := by
  intro g hg
  have hidx' : (S₀.subgroupOf S).index = 2 := hidx
  have hnorm : (S₀.subgroupOf S).Normal := normal_of_index_eq_two hidx'
  obtain ⟨s, hs, hgs⟩ := hfus g (hS₀ hg)
  rw [hgs] at hg
  have hmem : (⟨s⁻¹ * t * s, hS₀ hg⟩ : S) ∈ S₀.subgroupOf S := mem_subgroupOf.mpr hg
  have h := mem_subgroupOf.mp (hnorm.conj_mem _ hmem ⟨s, hs⟩)
  apply htS₀
  have e : s * (s⁻¹ * t * s) * s⁻¹ = t := by group
  simpa [e] using h

theorem s56_exists_sylow_eq {G : Type*} [Group G] [Finite G] (S : Subgroup G) (t : G)
    (hS : IsPGroup 2 S) (htS : t ∈ S)
    (hCS : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ centralizer ({t} : Set G))
      (centralizer ({t} : Set G)))
    (hfus : ∀ g : G, g⁻¹ * t * g ∈ S → ∃ s ∈ S, g⁻¹ * t * g = s⁻¹ * t * s) :
    ∃ P : Sylow 2 G, (P : Subgroup G) = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR, hSR⟩ : ∃ R : Subgroup G, IsSylowOf 2 R (normalizer (S : Set G)) ∧ S ≤ R := by
    obtain ⟨Q, hQ⟩ := (hS.comap_subtype (K := normalizer (S : Set G))).exists_le_sylow
    refine ⟨(Q : Subgroup (normalizer (S : Set G))).map (normalizer (S : Set G)).subtype,
      ⟨Q, rfl⟩, fun x hx => ?_⟩
    exact ⟨⟨x, le_normalizer hx⟩, hQ (mem_subgroupOf.mpr hx), rfl⟩
  have hRS : R ≤ S := by
    intro n hn
    have hnN : n ∈ normalizer (S : Set G) := hR.le hn
    have h1 : n⁻¹ * t * n ∈ S := (mem_normalizer_iff''.mp hnN t).mp htS
    obtain ⟨s, hs, hns⟩ := hfus n h1
    have hc : n * s⁻¹ ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_iff]
      intro h ht
      rw [Set.mem_singleton_iff] at ht
      subst ht
      calc h * (n * s⁻¹) = n * (n⁻¹ * h * n) * s⁻¹ := by group
        _ = n * (s⁻¹ * h * s) * s⁻¹ := by rw [hns]
        _ = n * s⁻¹ * h := by group
    have hcR : n * s⁻¹ ∈ R := mul_mem hn (inv_mem (hSR hs))
    have hEq : R ⊓ centralizer ({t} : Set G) = S ⊓ centralizer ({t} : Set G) :=
      hCS.eq_of_le (inf_le_inf_right _ hSR) inf_le_right hR.isPGroup.to_inf_left
    have hcS : n * s⁻¹ ∈ S ⊓ centralizer ({t} : Set G) := hEq ▸ ⟨hcR, hc⟩
    simpa using mul_mem hcS.1 hs
  rw [le_antisymm hRS hSR] at hR
  exact CFSG.LocalAnalysis.EvenBN.Common.exists_sylow_eq_of_isSylowOf_of_normalizer_le hR le_rfl

end CFSG.LocalAnalysis.EvenBN.Tits.S56
