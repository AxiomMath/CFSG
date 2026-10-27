module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Sp4
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Local

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def CFA6Diag : Prop :=
  ∀ (J₀ : Type) [Group J₀] [Finite J₀], IsSec8JType J₀ 3 1 → ∀ θ : MulAut J₀, θ * θ = 1 →
    (∃ O : Subgroup (MulAut J₀), O ≤ centralizer ({θ} : Set (MulAut J₀)) ∧ O ≠ ⊥ ∧
      Odd (Nat.card O) ∧
      (Eight.fixSubgroup θ).map (MulAut.conj : J₀ →* MulAut J₀) ≤ normalizer (O : Set _)) →
    Nat.card (Eight.fixSubgroup θ) = 10

@[expose] def CFA6SylowCent : Prop :=
  ∀ (J₀ : Type) [Group J₀] [Finite J₀], IsSec8JType J₀ 3 1 → ∀ D : Subgroup J₀,
    Nat.card D = 8 →
      Nat.card (centralizer ((D.map (MulAut.conj : J₀ →* MulAut J₀) : Subgroup (MulAut J₀)) :
        Set (MulAut J₀))) = 4 ∧ Nat.card (centralizer (D : Set J₀)) = 2

@[expose] def CFA6NoComm : Prop :=
  ∀ (J₀ : Type) [Group J₀] [Finite J₀], IsSec8JType J₀ 3 1 → ∀ θ₁ θ₂ : MulAut J₀,
    θ₁ * θ₁ = 1 → θ₂ * θ₂ = 1 → Nat.card (Eight.fixSubgroup θ₁) = 10 →
      θ₂ ∉ (MulAut.conj : J₀ →* MulAut J₀).range → ∀ D : Subgroup J₀, Nat.card D = 8 →
        θ₂ ∈ centralizer ((D.map (MulAut.conj : J₀ →* MulAut J₀) : Subgroup (MulAut J₀)) :
          Set (MulAut J₀)) → θ₁ * θ₂ ≠ θ₂ * θ₁

@[expose] def CFA6InnerInv : Prop :=
  ∀ (J₀ : Type) [Group J₀] [Finite J₀], IsSec8JType J₀ 3 1 → ∀ j : J₀, j * j = 1 → j ≠ 1 →
    Nat.card (centralizer ({j} : Set J₀)) = 8 ∧
      IsPGroup 2 (centralizer ({MulAut.conj j} : Set (MulAut J₀)))

end CFSG.ComponentClassification.GSThmB
