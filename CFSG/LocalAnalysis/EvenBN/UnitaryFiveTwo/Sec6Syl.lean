module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4R3

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

theorem exists_sylow_of_normalizer_le {G : Type*} [Group G] [Finite G] {T X : Subgroup G}
    (hT : IsPGroup 2 T) (hX : CFSG.ABGLocalTools.IsSylowOf 2 T X)
    (hNX : normalizer (T : Set G) ≤ X) : ∃ S : Sylow 2 G, (S : Subgroup G) = T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hTS⟩ := hT.exists_le_sylow
  refine ⟨S, ?_⟩
  by_contra hne
  have hlt : T < (S : Subgroup G) := lt_of_le_of_ne hTS (fun h => hne h.symm)
  obtain ⟨n, hnS, hnN, hnT⟩ := exists_mem_normalizer_not_mem_of_lt S.isPGroup' hlt
  have hnX : n ∈ X := hNX hnN
  have hle : T ⊔ zpowers n ≤ (S : Subgroup G) := sup_le hTS (zpowers_le.2 hnS)
  have hle2 : T ⊔ zpowers n ≤ X := sup_le hX.le (zpowers_le.2 hnX)
  have hp : IsPGroup 2 ↥(T ⊔ zpowers n) := S.isPGroup'.to_le hle
  have heq := hX.eq_of_le le_sup_left hle2 hp
  exact hnT (heq ▸ mem_sup_right (mem_zpowers n))

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
