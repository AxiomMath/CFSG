module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ClSp
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ClSU
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ClOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ClSL

public section

namespace CFSG.ComponentClassification.CatFC.DS81

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Open

theorem lie23To89_classical {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    (ht : t ∈ classicalTags) (hm : StatedClassicalModel X t n 2 f) (τ : X) (hτ : orderOf τ = 2)
    (h23 : 23 ∣ Nat.card ↥(centralizer ({τ} : Set X))) :
    89 ∣ Nat.card ↥(centralizer ({τ} : Set X)) := by
  cases t
  · exact ClSL.lie23To89_psl hm τ hτ h23
  · exact ClSU.lie23To89_psu hm τ hτ h23
  · exact ClSp.lie23To89_psp hm τ hτ h23
  · exact absurd rfl hm.1.2.2.2
  · exact ClOmega.lie23To89_pomegaPlus hm τ hτ h23
  · exact ClOmega.lie23To89_pomegaMinus hm τ hτ h23
  all_goals exact absurd ht (by decide)

theorem lie23To89At_classical : ∀ t ∈ classicalTags,
    ∀ (X : Type) [Group X] [Finite X] (n f : ℕ), StatedLieAdmissible t n 2 f →
      LieModel X t n 2 f → ∀ τ : X, orderOf τ = 2 →
        23 ∣ Nat.card ↥(centralizer ({τ} : Set X)) → 89 ∣ Nat.card ↥(centralizer ({τ} : Set X)) :=
  fun _ ht _ _ _ _ _ _ hX τ hτ h23 => lie23To89_classical ht (hX.statedClassicalModel ht) τ hτ h23

end CFSG.ComponentClassification.CatFC.DS81
