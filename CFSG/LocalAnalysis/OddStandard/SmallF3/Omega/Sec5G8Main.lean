module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5G8Shape
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5G8Dih
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Z8Sylow

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r ρ : G}
  {B A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G} {K₁ K₂ : Subgroup G} {a b : G}

theorem sec5g8_main (hB3 : GoldschmidtB3Tmp) (hSH8 : Sec5SH8Statement) (hy : Sec5B59Hyp)
    (h55 : Asc82Lemma55) (h58d : Asc82Lemma58d) (hFB : Asc82Sec5FactB5z)
    (h4 : Asc82FactReflCentQ6) (hU : Asc82FactPocketsUniq6) (hSq : Asc82FactSqReflQ6)
    (h : Sec510Ctx G t L S z r ρ B A φ) (hs : Sec510Stage1 G t L S z φ A K₁ K₂ a b)
    (hTE : sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) ≠ sec5p510_E t a b)
    {X : Type} [Group X] (π : ↥(centralizer ({z} : Set G)) →* X) (hπ : Function.Surjective π)
    (hker : π.ker = (zpowers z).subgroupOf (centralizer ({z} : Set G))) :
    Sec5G8Outcome (((sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))).subgroupOf
      (centralizer ({z} : Set G))).map π) := by
  haveI : Finite X := Finite.of_surjective π hπ
  have hTR : sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) =
      sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂) := hs.T_cases.resolve_left hTE
  obtain ⟨P, -, hle, hSC⟩ := sec5z8_exists_sylow_strongly_closed hy h55 h58d hFB h4 hU hSq h hs
    hTR π hπ hker
  exact sec5g8_outcome hB3 hSH8 P hle (sec5g8_dihedral hy h4 h hs hTE π hker) hSC

end CFSG.OddStandard.SmallF3.Omega
