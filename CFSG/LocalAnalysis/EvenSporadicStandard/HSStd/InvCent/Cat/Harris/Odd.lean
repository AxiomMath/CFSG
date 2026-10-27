module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harris.Props
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harris.Bridge
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClShapes

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harris

open Subgroup CFSG CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.CatFC
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput GLS3OddLieAutComponentsInput)


variable {G : Type} [Group G] [Finite G] {S : Subgroup G} [S.Normal] {t : G}

theorem odd_arm (hO : LieOrderFormulasInput) (hgls : GLS3OddLieAutComponentsInput)
    (aL : HarrisOddSharp .PSL 2 4) (aU : HarrisOddSharp .PSU 3 2) (aS : HarrisOddSharp .PSp 2 1)
    (wO : HarrisOmegaLarge .POmegaOdd 3 1) (wM : HarrisOmegaLarge .POmegaMinus 4 1)
    (kL : HarrisKleinFree .PSL 2 3 4) (kU : HarrisKleinFree .PSU 3 3 2)
    (kS : HarrisKleinFree .PSp 2 3 1)
    (h : Cfg G S t)
    (ζ : ↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6)))
    (hodd : OddLieType ↥S) :
    LieModel ↥S .PSU 4 3 1 ∨ LieModel ↥S .PSL 3 3 2 ∨ LieModel ↥S .PSL 4 3 1 := by
  have hσ : orderOf (MulAut.conjNormal t : MulAut ↥S) = 2 := orderOf_conjNormal h.cent h.ord
  obtain ⟨D, hDeq, hDhyp⟩ := harris_a6Hyp h ζ
  obtain ⟨tag, n, p, f, hp, hp2, hadm, hm⟩ := hodd
  obtain ⟨hp3, hshape, hswap⟩ :=
    oddA6Shape_of_inputs hO hgls tag ↥S n p f hp hp2 hadm hm _ hσ D hDhyp
  subst hp3
  have hdvd := Nat.le_of_dvd (by norm_num) (card_fixed_dvd (S := S) ζ)
  rcases hshape with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · obtain ⟨rfl, rfl, rfl⟩ := h1
    exact (excl_of_sharp h ζ (aL ↥S hm _ hσ D hDhyp) (kL ↥S hm _ hσ D hDhyp)).elim
  · obtain ⟨rfl, rfl, rfl⟩ := h2
    exact Or.inr (Or.inl hm)
  · obtain ⟨rfl, rfl, rfl⟩ := h3
    exact Or.inr (Or.inr hm)
  · obtain ⟨rfl, rfl, rfl⟩ := h4
    exact (excl_of_sharp h ζ (aU ↥S hm _ hσ D hDhyp) (kU ↥S hm _ hσ D hDhyp)).elim
  · obtain ⟨rfl, rfl, rfl⟩ := h5
    exact Or.inl hm
  · obtain ⟨rfl, rfl, rfl⟩ := h6
    exact (excl_of_sharp h ζ (aS ↥S hm _ hσ D hDhyp) (kS ↥S hm _ hσ D hDhyp)).elim
  · obtain ⟨rfl, rfl, rfl⟩ := h7
    obtain ⟨a, b, hab⟩ := hswap rfl rfl rfl
    exact (hab (by
      rw [hDeq]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))).elim
  · obtain ⟨rfl, rfl, rfl⟩ := h8
    have := wO ↥S hm _ hσ
    omega
  · obtain ⟨rfl, rfl, rfl⟩ := h9
    have := wM ↥S hm _ hσ
    omega

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harris
