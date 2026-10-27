module

public import CFSG.LocalAnalysis.SectionRank.LargeRee.Suzuki
public import CFSG.LocalAnalysis.SectionRank.LargeRee.Catalog

public section

namespace CFSG.SectionRank.LargeRee

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Simplicity

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem rankOneCells_one
    (ha : 1 ≤ a) (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) :
    RankOneCells a 1 (blockT a hK 1) := by
  intro x hx
  have hn := relNrepHom_mem_r2 hK
  exact r2_cells hK ha (mul_mem (mul_mem hn (blockX_le_r2 hK hx)) hn)

theorem rankOneSection_one
    (ha : 1 ≤ a) (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1))
    {E : Type*} [Group E] [Finite E] {π : E →* reeFixed ReeTag.F4 K a}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) : RankOneSection a π 1 (blockT a hK 1) := by
  set e := r2EquivSuzuki K a hK ha
  obtain ⟨ρ, hρ⟩ := exists_suzukiGroup_lift ha hK hπ hcen hodd
    ((r2 K a hK).subtype.comp e.symm.toMonoidHom)
  refine ⟨r2 K a hK, ρ.comp e.toMonoidHom, fun g => ?_, blockX_le_r2 hK, blockT_le_r2 hK,
    relNrepHom_mem_r2 hK⟩
  have h := DFunLike.congr_fun hρ (e g)
  simpa using h

theorem suzukiBlockInputs :
    SuzukiBlockInputs := fun _ _ _ _ _ ha hK =>
  ⟨rankOneCells_one ha hK, fun _ _ _ _ hπ hcen hodd => rankOneSection_one ha hK hπ hcen hodd⟩

theorem catalog_large_ree :
    LargeReeCatalogHyp :=
  catalog_large_ree_of_suzuki suzukiBlockInputs

end CFSG.SectionRank.LargeRee
