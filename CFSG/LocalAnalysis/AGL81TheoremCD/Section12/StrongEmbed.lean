module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem stronglyDEmbedded_of_almost {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}
    (h : TwelveCtx G M p Q H) (hns : ¬ Group.IsSolvable M) (d : ℕ) (hd : d ∈ sigmaSet G M) :
    ∃ P : Sylow d G, (P : Subgroup G) ≤ M ∧ rankThreeGamma 1 d (P : Subgroup G) ≤ M := by
  obtain ⟨P, hPM, -, hcases⟩ := h.cstar.almost M h.maxLocal d hd
  refine ⟨P, hPM, ?_⟩
  rcases hcases with h1 | h2 | h3
  · exact h1
  · exact absurd h2.2.1 hns
  · exact absurd h3.2.1 hns

theorem not_isSolvable_of_mem_weakBlockSet {M H L : Subgroup G}
    (hL : L ∈ weakBlockSet M H) : ¬ Group.IsSolvable M := by
  intro hsol
  have hLM : L ≤ M := hL.le
  haveI : Group.IsSolvable ↥M := hsol
  have hLs : Group.IsSolvable ↥L :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hLM).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLM).surjective
  have hLne : L ≠ ⊥ := by
    intro hbot
    rw [hbot] at hL
    exact hL.not_le_normalizer bot_le
  haveI : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).mpr hLne
  haveI : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL.perfect
  exact Group.IsPerfect.not_isSolvable ↥L hLs

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
