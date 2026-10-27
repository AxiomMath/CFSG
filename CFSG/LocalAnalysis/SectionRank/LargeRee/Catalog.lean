module

public import CFSG.LocalAnalysis.SectionRank.LargeRee.Split
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwoData
public import CFSG.LocalAnalysis.SectionRank.ExceptionalEvenCatalog
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover

public section

namespace CFSG.SectionRank.LargeRee

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Simplicity

@[expose] def SuzukiBlockInputs
    : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime] (a : ℕ), 1 ≤ a →
    ∀ hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1),
      RankOneCells a 1 (blockT a hK 1) ∧
        ∀ (E : Type) [Group E] [Finite E] (π : E →* reeFixed ReeTag.F4 K a),
          Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
            RankOneSection a π 1 (blockT a hK 1)

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem large_ree_section_of_suzuki
    (hsz : SuzukiBlockInputs) (ha : 1 ≤ a)
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) {E : Type} [Group E] [Finite E]
    {π : E →* reeFixed ReeTag.F4 K a} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) :
    ∃ s : reeFixed ReeTag.F4 K a →* E, ∀ x, π (s x) = x := by
  obtain ⟨hcells1, hsec1⟩ := hsz K a ha hK
  refine exists_section_of_rankOne hK hπ hcen hodd (fun i => ?_) (fun i => ?_)
  · match i with
    | 0 => exact rankOneCells_zero hK
    | 1 => exact hcells1
  · match i with
    | 0 => exact rankOneSection_zero hK hπ hcen hodd
    | 1 => exact hsec1 E π hπ hcen hodd

theorem large_ree_perfect_odd_cover_trivial_of_suzuki
    (hsz : SuzukiBlockInputs) (ha : 1 ≤ a)
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) {E : Type} [Group E] [Finite E]
    [Group.IsPerfect E] (π : E →* reeFixed ReeTag.F4 K a) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  obtain ⟨s, hs⟩ := large_ree_section_of_suzuki hsz ha hK hπ hcen hodd
  exact ker_eq_bot_of_section_of_perfect π hcen s hs

theorem catalog_large_ree_of_suzuki
    (hsz : SuzukiBlockInputs) : LargeReeCatalogHyp := by
  intro L _ _ hL hSQT hodd f h
  have : Group.IsPerfect L := hL.1
  obtain ⟨K, _, _, _, a, ha, hK, ⟨e⟩⟩ := exists_mulEquiv_reeFixed_of_model h
  exact (catalogStepConclusion_of_perfect_odd_cover_trivial hSQT hodd e
    fun π hπ hC hπodd =>
      large_ree_perfect_odd_cover_trivial_of_suzuki hsz ha hK π hπ hC hπodd).2

end CFSG.SectionRank.LargeRee
