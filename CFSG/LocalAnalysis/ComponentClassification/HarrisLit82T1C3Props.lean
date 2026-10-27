module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Defs
public import CFSG.GH74.GLS.Bg.Local.Transfer1515

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup
open CFSG.GH74.GLS.Bg.Thompson (IsSylowIn)

@[expose] def fixedSubgroup {X : Type*} [Group X] (α : MulAut X) : Subgroup X where
  carrier := {x | α x = x}
  mul_mem' {a b} (ha : α a = a) (hb : α b = b) := by
    change α (a * b) = a * b
    rw [map_mul, ha, hb]
  one_mem' := map_one α
  inv_mem' {a} (ha : α a = a) := by
    change α a⁻¹ = a⁻¹
    rw [map_inv, ha]

theorem mem_fixedSubgroup {X : Type*} [Group X] {α : MulAut X} {x : X} :
    x ∈ fixedSubgroup α ↔ α x = x :=
  Iff.rfl

@[expose] def Harris82Lemma410Rest : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    IsCoverOf .POmegaOdd 3 p f 2 X → ∀ z ∈ center X, z ≠ 1 →
    (∀ S₀ : Subgroup X, IsSylowIn 2 S₀ ⊤ →
      ∀ x ∈ S₀, (∀ y ∈ S₀, x * y = y * x) → x = 1 ∨ x = z) ∧
    ∀ t : X, orderOf t = 2 → t ∉ center X →
      (∀ J : Subgroup X, IsTwoComponentIn J (centralizer {t}) →
        IsSLTwoOver (p ^ f) (↥J ⧸ pPrimeCore 2 ↥J) ∧ (z ∈ J ∨ t ∈ J ∨ z * t ∈ J)) ∧
      (∀ J J' : Subgroup X, IsTwoComponentIn J (centralizer {t}) →
        IsTwoComponentIn J' (centralizer {t}) → ∀ e ∈ ({z, t, z * t} : Set X), e ∈ J → e ∈ J' →
          J = J') ∧
      ∀ T₀ : Subgroup X, IsSylowIn 2 T₀ (centralizer {t}) →
        closure {x | x ∈ T₀ ∧ x * x = 1} = T₀

@[expose] def Harris82Lemma411U1 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    IsCoverOf .POmegaOdd 3 p f 2 X → ∀ z ∈ center X, z ≠ 1 →
    ∀ α : MulAut X, α * α = 1 →
      (∃ x : X, x * x = 1 ∧ x ∉ center X ∧ α = MulAut.conj x) ∨
        ∃ J : Subgroup X, IsTwoComponentIn J (fixedSubgroup α) ∧ z ∈ J ∧
          ¬ IsSLTwoOver (p ^ f) (↥J ⧸ pPrimeCore 2 ↥J)

@[expose] def Harris82Lemma411U2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    IsCoverOf .POmegaOdd 3 p f 2 X → ∀ t : X, orderOf t = 2 → t ∉ center X →
    pPrimeCore 2 ↥(centralizer ({t} : Set X)) = ⊥ ∧
      ∀ α : MulAut X,
        (∀ J : Subgroup X, IsTwoComponentIn J (centralizer {t}) → ∀ j ∈ J, α j = j) →
          α = 1 ∨ α = MulAut.conj t

@[expose] def Harris82Lemma411U3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    IsCoverOf .POmegaOdd 3 p f 2 X →
    ∀ α β : MulAut X, ∃ x : X, α * β * α⁻¹ * β⁻¹ = MulAut.conj x

@[expose] def Harris82Lemma411U4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    IsCoverOf .POmegaOdd 3 p f 2 X → ∀ C P : Subgroup (MulAut X),
    (MulAut.conj : X →* MulAut X).range ≤ C → IsSylowIn 2 P C →
    ∃ V : Subgroup (MulAut X), V ≤ P ∧ P ⊓ (MulAut.conj : X →* MulAut X).range ≤ V ∧
      (∀ s ∈ P, ∀ v ∈ V, s * v * s⁻¹ ∈ V) ∧
      (∀ v ∈ V, ∀ w ∈ V, v ∉ (MulAut.conj : X →* MulAut X).range →
        w ∉ (MulAut.conj : X →* MulAut X).range → v⁻¹ * w ∈ (MulAut.conj : X →* MulAut X).range) ∧
      (∃ b ∈ P, ∀ s ∈ P, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ V) ∧
      (∀ v ∈ V, v * v = 1 → v ∈ (MulAut.conj : X →* MulAut X).range) ∧
      ((∃ s ∈ P, s ∉ V) →
        ∃ x ∈ P, x ∉ (MulAut.conj : X →* MulAut X).range ∧ x * x = 1)

@[expose] def Harris82Lemma51e : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (p : ℕ), p.Prime → p ≠ 2 →
    IsSimpleChevalleyOver p X → ∀ z : X, orderOf z = 2 → ∀ J : Subgroup X,
    IsTwoComponentIn J (centralizer {z}) → z ∈ J → ∀ r : ℕ, 5 ≤ p ^ r →
      ¬ IsCoverOf .POmegaOdd 3 p r 2 (↥J ⧸ pPrimeCore 2 ↥J)

@[expose] def Harris82Lemma58Spin7 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsTwoQuasisimple K → ∀ p : ℕ, p.Prime → p ≠ 2 →
    IsSimpleChevalleyOver p (K ⧸ Open.fusionZStar K) →
    ∀ z₁ z₂ : K, orderOf z₁ = 2 → z₁ ∈ center K → orderOf z₂ = 2 →
    (QuotientGroup.mk z₂ : K ⧸ pPrimeCore 2 K) ∉ center (K ⧸ pPrimeCore 2 K) →
    ∀ L₁ L₂ : Subgroup K, IsTwoComponentIn L₁ (centralizer {z₂}) →
    IsTwoComponentIn L₂ (centralizer {z₂}) → z₁ ∈ L₁ → z₂ ∈ L₂ → ∀ k : ℕ, 5 ≤ p ^ k →
    IsSLTwoOver (p ^ k) (↥L₁ ⧸ pPrimeCore 2 ↥L₁) → ∀ r : ℕ, 5 ≤ p ^ r →
      ¬ IsCoverOf .POmegaOdd 3 p r 2 (↥L₂ ⧸ pPrimeCore 2 ↥L₂)

@[expose] def Harris82Theorem1SpinSevenThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G → ¬ Blueprint.Catalog G →
    ∀ z : G, orderOf z = 2 → ∀ L : Subgroup G, IsTwoComponentIn L (centralizer {z}) → z ∈ L →
    ∀ p f : ℕ, p.Prime → p ^ f = 3 → IsMTypeSchur p ↥L →
      ¬ IsCoverOf .POmegaOdd 3 p f 2 (↥L ⧸ pPrimeCore 2 ↥L)

end CFSG.ComponentClassification.HarrisLit.T1
