module

public import CFSG.LocalAnalysis.SectionRank.SuzukiCover
public import CFSG.LieType.Steinberg.CentralExt.Families
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic
public import CFSG.LocalAnalysis.SectionRank.EvenCover.CoverMap
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearSplit

public section

namespace CFSG.SectionRank.EvenCover

open CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg CFSG.LieType.CentralExt

theorem even_symplectic_central_odd_extension_splitting
    {K : Type} [Field K] [Finite K]
    [CharP K 2] (r : ℕ) {E : Type*} [Group E] [Finite E] {π : E →* StatedSp r K}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) :
    ∃ σ : StatedSp r K →* E, (∀ g, π (σ g) = g) ∧
      (∀ τ : StatedSp r K →* E, (∀ g, π (τ g) = g) → τ = σ) ∧
      ∃ e : π.ker × σ.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := not_two_dvd_of_odd hodd
  refine exists_section_mulEquiv_of_existsUnique hcen
    (sp_existsUnique_section_of_sl2_lift (p := 2) r hπ hcen hC fun ρ => ?_)
  obtain ⟨ρ', hρ', -⟩ := sl2_existsUnique_lift hπ hcen hC ρ
  exact ⟨ρ', fun g => congrArg (· g) hρ'⟩

theorem statedScalars_subgroupOf_statedSp_eq_bot {K : Type} [Field K] [CharP K 2] (n : ℕ) :
    (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) = ⊥ :=
  CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot

theorem center_eq_bot_of_even_symplectic
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    (hodd : Odd (Nat.card (Subgroup.center L)))
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedSp n K)) : Subgroup.center L = ⊥ := by
  obtain ⟨hsurj, hcen, hdvd⟩ := pullbackFst_centralQuotientMap e
  obtain ⟨σ, hσ, -⟩ := even_symplectic_central_odd_extension_splitting n hsurj hcen
    (Odd.of_dvd_nat hodd hdvd)
  obtain ⟨φ, -, -, hD⟩ := perfect_cover_map_of_section e σ hσ
  rw [← hD, statedScalars_subgroupOf_statedSp_eq_bot, Subgroup.map_bot]

theorem even_symplectic_odd_cover_catalog_step
    {L : Type} [Group L] [Finite L]
    (hL : IsQuasisimple L) (hodd : Odd (Nat.card (Subgroup.center L))) {n f : ℕ}
    (h : StatedClassicalModel (L ⧸ Subgroup.center L) .PSp n 2 f) :
    Subgroup.center L = ⊥ ∧ (IsStronglyQuasithin L → CatalogStepConclusion L) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := ClassicalOdd.charP_of_card hK
  have : Group.IsPerfect L := hL.1
  have hZ := center_eq_bot_of_even_symplectic hodd e
  exact ⟨hZ, fun hSQT => catalogStepConclusion_of_center_eq_bot hSQT hZ⟩

end CFSG.SectionRank.EvenCover
