module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def CF81L2CentPerfect : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    Blueprint.LieModel Y .PSL 2 p f → ∀ y₀ : Y, orderOf y₀ = 2 →
      ∀ R : Subgroup (MulAut Y), R ≤ centralizer ({MulAut.conj y₀} : Set (MulAut Y)) →
        Group.IsPerfect R → R = ⊥

@[expose] def CF81L2NineCent : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Blueprint.LieModel Y .PSL 2 3 2 → ∀ y₀ : Y,
    orderOf y₀ = 2 → IsPGroup 2 ↥(centralizer ({MulAut.conj y₀} : Set (MulAut Y)))

@[expose] def CF81Sp4Three : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), p.Prime → 1 ≤ f →
    Blueprint.LieModel X .PSp 2 3 1 → Blueprint.LieModel X .PSp 2 p f → p ^ f = 3

end CFSG.ComponentClassification.GSThmB
