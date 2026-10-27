module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBSymplecticTwo
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def Lemma2_4_23_five_exam : Prop :=
  Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
    ∀ s ∈ S, s ∉ thompsonJ S → s ^ 2 = 1 → centerOf L ≠ ⊥ → 4 < 2 ^ n →
      ∀ x ∈ T ⊓ Subgroup.centralizer ({s} : Set G), x ∉ S →
        ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ (n / 2) ∧
          ∃ e : ↥(L ⊓ Subgroup.centralizer ({s} : Set G) ⊔
              conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x : Subgroup G) ≃*
              StatedProj (StatedSp 2 F),
            ∀ β : MulAut ↥(L ⊓ Subgroup.centralizer ({s} : Set G) ⊔
                conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x : Subgroup G),
              (∀ k, ((β k : ↥(L ⊓ Subgroup.centralizer ({s} : Set G) ⊔
                conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x : Subgroup G)) : G) =
                x * (k : G) * x⁻¹) →
              MulAut.congr e β ∉ typeKernel F

@[expose] def Sp4OutCyclic : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (e : ℕ), Fintype.card F = 2 ^ e → 0 < e →
    IsCyclic (Outer (StatedProj (StatedSp 2 F))) ∧
      Nat.card (Outer (StatedProj (StatedSp 2 F))) = 2 * e

end CFSG.QuasithinUnique.Lin2
