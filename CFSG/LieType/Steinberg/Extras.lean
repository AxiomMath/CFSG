module

public import CFSG.LieType.Steinberg.Basic
public import CFSG.LieType.Universal.RootData

public section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.Universal CFSG.LieType.CurtisTits
open scoped commutatorElement

variable {K : Type*} [Group K]

@[expose] def ProdInjectiveFor {ι : Type*} (X : (ι → ℤ) → Subgroup K) (L : List (ι → ℤ)) :
    Prop :=
  ∀ f g : (ι → ℤ) → K, (∀ γ ∈ L, f γ ∈ X γ) → (∀ γ ∈ L, g γ ∈ X γ) →
    (L.map f).prod = (L.map g).prod → ∀ γ ∈ L, f γ = g γ

structure SteinbergExtras (D : UniversalRootDatum K) (n : Fin D.rank → K)
    (H : Fin D.rank → Subgroup K) : Prop where
  ne_bot : ∀ γ ∈ D.roots, D.rootGroup γ ≠ ⊥
  two_smul_le : ∀ γ ∈ D.roots, 2 • γ ∈ D.roots → D.rootGroup (2 • γ) ≤ D.rootGroup γ
  commutator_mem : ∀ γ ∈ D.roots, ∀ δ ∈ D.roots, LinIndepPair γ δ →
    ∀ x ∈ D.rootGroup γ, ∀ y ∈ D.rootGroup δ,
      ⁅x, y⁆ ∈ ⨆ ε ∈ openCone D.roots γ δ, D.rootGroup ε
  prodInjective_pos : ∀ L : List (Fin D.rank → ℤ), L.Nodup →
    (∀ γ, γ ∈ L ↔ γ ∈ D.roots ∧ 0 < ht γ ∧ ∀ δ ∈ D.roots, γ ≠ 2 • δ) →
    L.Pairwise (fun γ δ => ht γ ≤ ht δ) → ProdInjectiveFor D.rootGroup L
  prodInjective_neg : ∀ L : List (Fin D.rank → ℤ), L.Nodup →
    (∀ γ, γ ∈ L ↔ γ ∈ D.roots ∧ ht γ < 0 ∧ ∀ δ ∈ D.roots, γ ≠ 2 • δ) →
    L.Pairwise (fun γ δ => ht δ ≤ ht γ) → ProdInjectiveFor D.rootGroup L
  posPart_inf_negPart : (⨆ γ ∈ {γ | γ ∈ D.roots ∧ 0 < ht γ}, D.rootGroup γ) ⊓
    (⨆ γ ∈ {γ | γ ∈ D.roots ∧ ht γ < 0}, D.rootGroup γ) = ⊥
  rankOne_bruhat : ∀ i, ∀ g ∈ rankOne D.rootGroup i,
    (∃ h ∈ H i, ∃ u ∈ D.rootGroup (Pi.single i 1), g = h * u) ∨
      ∃ u ∈ D.rootGroup (Pi.single i 1), ∃ h ∈ H i, ∃ v ∈ D.rootGroup (Pi.single i 1),
        g = u * n i * h * v
  eq_one_of_mem_normalizer : ∀ i, ∀ u ∈ D.rootGroup (Pi.single i 1),
    u ∈ Subgroup.normalizer (D.rootGroup (-Pi.single i 1) : Set K) → u = 1
  torus_commute : ∀ i j, ∀ h ∈ H i, ∀ h' ∈ H j, Commute h h'
  torus_iSupIndep : iSupIndep H
  torus_inf_posPart : (⨆ i, H i) ⊓ (⨆ γ ∈ {γ | γ ∈ D.roots ∧ 0 < ht γ}, D.rootGroup γ) = ⊥

end CFSG.LieType.Steinberg
