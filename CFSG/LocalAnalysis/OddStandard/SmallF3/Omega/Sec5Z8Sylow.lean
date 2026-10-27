module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Z8Quot
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5ZGold
public import CFSG.Open.FusionDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r ρ : G}
  {B A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G} {K₁ K₂ : Subgroup G} {a b : G}

theorem sec5z8_exists_sylow_strongly_closed (hy : Sec5B59Hyp) (h55 : Asc82Lemma55)
    (h58d : Asc82Lemma58d) (hFB : Asc82Sec5FactB5z) (h4 : Asc82FactReflCentQ6)
    (hU : Asc82FactPocketsUniq6) (hSq : Asc82FactSqReflQ6)
    (h : Sec510Ctx G t L S z r ρ B A φ) (hs : Sec510Stage1 G t L S z φ A K₁ K₂ a b)
    (hTR : sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) =
      sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))
    {X : Type} [Group X] (π : ↥(centralizer ({z} : Set G)) →* X) (hπ : Function.Surjective π)
    (hker : π.ker = (zpowers z).subgroupOf (centralizer ({z} : Set G))) :
    ∃ P : Sylow 2 X, (P : Subgroup X) = (S.subgroupOf (centralizer ({z} : Set G))).map π ∧
      ((sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))).subgroupOf
        (centralizer ({z} : Set G))).map π ≤ (P : Subgroup X) ∧
      CFSG.Open.fusionStronglyClosed
        ((((sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))).subgroupOf
          (centralizer ({z} : Set G))).map π : Subgroup X) : Set X) (P : Subgroup X) := by
  obtain ⟨P, hP⟩ := sec5z_exists_sylow_quotient h π hπ
  have hTS : sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) ≤ S :=
    (sec5p510_T_le_R t z _).trans inf_le_left
  refine ⟨P, hP, ?_, ?_⟩
  · rw [hP]
    rintro x ⟨y, hy, rfl⟩
    exact ⟨y, Subgroup.mem_subgroupOf.mpr (hTS (Subgroup.mem_subgroupOf.mp hy)), rfl⟩
  · rw [hP]
    intro c hc g hg
    exact sec5z8_strongly_closed_quotient hy h55 h58d hFB h4 hU hSq h hs hTR π hπ hker
      c hc g hg

end CFSG.OddStandard.SmallF3.Omega
