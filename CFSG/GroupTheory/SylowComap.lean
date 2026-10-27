module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG

@[expose] noncomputable def sylowComapOfKerIsPGroup {G H : Type*} [Group G] [Group H] {p : ℕ}
    (π : G →* H) (hπ : Function.Surjective π) (hker : IsPGroup p π.ker) (U : Sylow p H) :
    Sylow p G :=
  U.comapOfKerIsPGroup π hker (by
    rw [π.range_eq_top_of_surjective hπ]
    exact le_top)

@[simp]
theorem coe_sylowComapOfKerIsPGroup {G H : Type*} [Group G] [Group H] {p : ℕ}
    (π : G →* H) (hπ : Function.Surjective π) (hker : IsPGroup p π.ker)
    (U : Sylow p H) :
    (sylowComapOfKerIsPGroup π hπ hker U : Subgroup G) = U.comap π :=
  rfl

@[expose] noncomputable def sylowComapOfInjective {G H : Type*} [Group G] [Group H] {p : ℕ}
    (π : G →* H) (hπ : Function.Surjective π) (hinj : Function.Injective π) (U : Sylow p H) :
    Sylow p G :=
  U.comapOfInjective π hinj (by
    rw [π.range_eq_top_of_surjective hπ]
    exact le_top)

@[simp]
theorem coe_sylowComapOfInjective {G H : Type*} [Group G] [Group H] {p : ℕ}
    (π : G →* H) (hπ : Function.Surjective π) (hinj : Function.Injective π)
    (U : Sylow p H) :
    (sylowComapOfInjective π hπ hinj U : Subgroup G) = U.comap π :=
  rfl

@[expose] noncomputable def sylowComapOfKerLeCenter {G H : Type*} [Group G] [Group H]
    (π : G →* H) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center G) (hcenter : Subgroup.center G = ⊥) (U : Sylow 2 H) :
    Sylow 2 G :=
  have hkerbot : π.ker = ⊥ :=
    le_bot_iff.mp (hker.trans (le_of_eq hcenter))
  sylowComapOfInjective π hπ ((MonoidHom.ker_eq_bot_iff π).mp hkerbot) U

@[simp]
theorem coe_sylowComapOfKerLeCenter {G H : Type*} [Group G] [Group H]
    (π : G →* H) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center G) (hcenter : Subgroup.center G = ⊥) (U : Sylow 2 H) :
    (sylowComapOfKerLeCenter π hπ hker hcenter U : Subgroup G) = U.comap π :=
  rfl

end CFSG
