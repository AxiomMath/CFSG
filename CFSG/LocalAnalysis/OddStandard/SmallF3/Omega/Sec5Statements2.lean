module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Lemma58b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G) (B A : Subgroup G),
    Sec5RCtx G t L S z r B A →
      ∀ B' : Subgroup G, B' ≤ A → (∀ m ∈ normalizer (A : Set G), ∀ b ∈ B', m * b * m⁻¹ ∈ B') →
        B' = ⊥ ∨ B' = A

@[expose] def Asc82Lemma58d : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G) (B A : Subgroup G),
    Sec5RCtx G t L S z r B A →
      ∃ φ : (Fin 6 → ZMod 2) → G,
        IsPermModuleVia (n := 6) (fun _ => True) φ A (L ⊓ normalizer (A : Set G))
            (alternatingGroup (Fin 6)) ∧
          φ (fun _ => 1) = t ∧ (∃ i : Fin 6, φ (Pi.single i 1) = r) ∧
          (∃ v, vecWeight v = 4 ∧ φ v = z) ∧
          (∀ v, φ v ∈ L ↔ IsEvenVec v) ∧
          (∀ v, vecWeight v = 1 ∨ vecWeight v = 5 →
            ∃ α : ℤˣ, InducesTypeSome L (φ v) 6 (-1) 1 α) ∧
          (∀ v, vecWeight v = 3 → ∃ α : ℤˣ, InducesTypeSome L (φ v) 6 (-1) 3 α)

@[expose] def Asc82Lemma510 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G) (B A : Subgroup G),
    Sec5RCtx G t L S z r B A → Case59Two t z A

@[expose] def Asc82Lemma512b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G) (B A : Subgroup G),
    Sec5RCtx G t L S z r B A → centerIn L = zpowers t

@[expose] def Asc82Lemma512K : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G) (B A : Subgroup G),
    Sec5RCtx G t L S z r B A → centerIn L = zpowers t →
      ∃ K₁ K₂ : Subgroup G, Sec5KCtx G t L S z r B A K₁ K₂

@[expose] def Asc82Lemma512H : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G) (B A K₁ K₂ : Subgroup G),
    Sec5KCtx G t L S z r B A K₁ K₂ → ∃ h : G, Sec5HCtx G t L S z r B A K₁ K₂ h

end CFSG.OddStandard.SmallF3.Omega
