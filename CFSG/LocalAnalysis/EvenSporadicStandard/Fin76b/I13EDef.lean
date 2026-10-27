module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Finish

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

@[expose] def innAutE {G : Type*} [Group G] (E : Subgroup G) : Subgroup (MulAut ↥E) :=
  (MulAut.conj : ↥E →* MulAut ↥E).range

structure EPi {G : Type*} [Group G] (E : Subgroup G) (π : MulAut ↥E →* Equiv.Perm (Fin 5)) :
    Prop where
  surj : Function.Surjective π
  ker : ∀ φ : MulAut ↥E, π φ = 1 ↔ φ ∈ innAutE E

@[expose] def BInv {G : Type*} [Group G] (E : Subgroup G)
    (π : MulAut ↥E →* Equiv.Perm (Fin 5)) (φ : MulAut ↥E) : Prop :=
  φ * φ = 1 ∧ π φ ∈ alternatingGroup (Fin 5) ∧ φ ∉ innAutE E

structure EFacts613 {G : Type*} [Group G] (E : Subgroup G) (t : G) : Prop where
  exists_pi : ∃ π : MulAut ↥E →* Equiv.Perm (Fin 5), EPi E π ∧
    (∀ φ : MulAut ↥E, BInv E π φ →
      Nat.card {e : ↥E // φ e = e} = 4 ∧ ∀ e : ↥E, φ e = e → e * e = 1) ∧
    (∀ φ : MulAut ↥E, BInv E π φ → ∀ e : ↥E, e * φ e = 1 → ∃ c : ↥E, e * φ c = c) ∧
    (∀ φ₁ φ₂ : MulAut ↥E, BInv E π φ₁ → BInv E π φ₂ → φ₁ * φ₂ = φ₂ * φ₁ → φ₁ ≠ φ₂ →
      φ₁ * φ₂ ∉ innAutE E →
      (∀ e : ↥E, φ₁ e = e → φ₂ e = e) ∧
      (∃ e₀ : ↥E, Subgroup.closure ({e₀, φ₁ e₀, φ₂ e₀, φ₁ (φ₂ e₀)} : Set ↥E) = ⊤) ∧
      Nat.card ↥(innAutE E ⊔ Subgroup.closure ({φ₁, φ₂} : Set (MulAut ↥E))) = 64 ∧
      ∀ ψ ∈ innAutE E ⊔ Subgroup.closure ({φ₁, φ₂} : Set (MulAut ↥E)), ψ * ψ = 1 →
        16 ≤ Nat.card ↥((innAutE E ⊔ Subgroup.closure ({φ₁, φ₂} : Set (MulAut ↥E))) ⊓
          Subgroup.centralizer ({ψ} : Set (MulAut ↥E))))

end CFSG.EvenSporadicStandard.Fin76b
