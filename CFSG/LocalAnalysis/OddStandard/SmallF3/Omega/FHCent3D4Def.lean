module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82FactCent3D4 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (H : Subgroup A), H.Normal →
    centralizer (H : Set A) = ⊥ → LieModel ↥H .POmegaPlus 4 3 1 →
    ∀ a : A, orderOf a = 2 → ∀ g : A, orderOf g = 3 → g * a = a * g → g ∉ H →
      ¬ ∀ c ∈ H ⊓ centralizer ({a} : Set A), Odd (orderOf c) → g * c = c * g

end CFSG.OddStandard.SmallF3.Omega
