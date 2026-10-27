module

public import CFSG.Quasithin.Background.PushS3Klein
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.QuasithinUnique.Setup.Lift.Piece

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Wreath CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement

section Klein

variable {G : Type} [Group G]

noncomputable def actOn (U P : Subgroup G) (hPU : P ≤ Subgroup.normalizer (U : Set G)) :
    ↥P →* MulAut ↥U :=
  CFSG.Quasithin.F6.PushS3.actOn U P hPU

theorem actOn_eq_one_iff {U P : Subgroup G} (hPU : P ≤ Subgroup.normalizer (U : Set G)) (p : ↥P) :
    actOn U P hPU p = 1 ↔ ∀ u : ↥U, (p : G) * u = u * p :=
  CFSG.Quasithin.F6.PushS3.actOn_eq_one_iff hPU p

theorem exists_induce_of_orders {U P : Subgroup G} [IsKleinFour ↥U]
    (hPU : P ≤ Subgroup.normalizer (U : Set G)) {p₁ p₂ : ↥P}
    (h3 : actOn U P hPU p₁ ^ 3 = 1) (h31 : actOn U P hPU p₁ ≠ 1) {k : ℕ}
    (h2 : actOn U P hPU p₂ ^ 2 ^ k = 1) (h21 : actOn U P hPU p₂ ≠ 1) :
    ∀ σ : MulAut ↥U, ∃ p : ↥P, ∀ u : ↥U, ((σ u : ↥U) : G) = (p : G) * (u : G) * (p : G)⁻¹ :=
  CFSG.Quasithin.F6.PushS3.exists_induce_of_orders hPU h3 h31 h2 h21

theorem isTwoReduced_of_induce {U P : Subgroup G} [IsKleinFour ↥U] (hUP : U ≤ P)
    (hPU : P ≤ Subgroup.normalizer (U : Set G)) (helem : IsElemAbelian 2 U)
    (hind : ∀ σ : MulAut ↥U, ∃ p : ↥P,
      ∀ u : ↥U, ((σ u : ↥U) : G) = (p : G) * (u : G) * (p : G)⁻¹) :
    IsTwoReducedIn P U :=
  CFSG.Quasithin.F6.PushS3.isTwoReduced_of_induce hUP hPU helem hind

end Klein

end CFSG.QuasithinUnique.Setup.Lift.Piece
