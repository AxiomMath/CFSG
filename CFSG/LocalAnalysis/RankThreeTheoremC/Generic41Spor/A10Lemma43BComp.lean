module

public import CFSG.Open.Defs
import CFSG.GroupTheory.LocalCores.Components
import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10B123

open CFSG.Open Subgroup

variable {Y : Type} [Group Y] [Finite Y]

theorem comp_commute {J₁ J₂ : Subgroup Y} (h₁ : IsComponentOf J₁ ⊤) (h₂ : IsComponentOf J₂ ⊤)
    (hne : J₁ ≠ J₂) : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a := by
  rcases CFSG.LocalCores.distinct_components_commute ((CFSG.isComponent_iff_open J₁).2 h₁)
      ((CFSG.isComponent_iff_open J₂).2 h₂) with h | h
  · exact absurd h hne
  · intro a ha b hb
    have hmem : a ∈ Subgroup.centralizer (J₂ : Set Y) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) ha
    exact (Subgroup.mem_centralizer_iff.mp hmem b hb).symm

theorem comp_conj {J : Subgroup Y} (hJ : IsComponentOf J ⊤) (y : Y) :
    IsComponentOf (J.map (MulAut.conj y).toMonoidHom) ⊤ :=
  (CFSG.isComponent_iff_open _).1
    (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj y) ((CFSG.isComponent_iff_open J).2 hJ))

theorem mem_normalizer_of_comp {K J : Subgroup Y} (hK : IsComponentOf K ⊤) (hJ : IsComponentOf J ⊤)
    {a : Y} (ha : a ∈ K) : a ∈ normalizer (J : Set Y) := by
  by_cases hKJ : K = J
  · subst hKJ
    exact Subgroup.le_normalizer ha
  · exact Subgroup.centralizer_le_normalizer (J : Set Y)
      (Subgroup.mem_centralizer_iff.mpr fun h hh => (comp_commute hK hJ hKJ a ha h hh).symm)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10B123
