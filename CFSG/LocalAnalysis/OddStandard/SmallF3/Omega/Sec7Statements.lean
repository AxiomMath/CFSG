module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Lemma71 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    IsOmega6Plus L → InCStar L

@[expose] def Asc82Lemma72 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    IsOmega6Plus L → ∀ P : Subgroup G, IsSylow2Of P (centralizer (L : Set G)) → IsCyclic P

@[expose] def Asc82Lemma73 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec7Ctx G t L S z →
    ∀ g : G, g⁻¹ * z * g ∈ centralizer ({t} : Set G) →
      (∃ α : ℤˣ, InducesTypeSome L (g⁻¹ * z * g) 6 1 3 α) ∨
        InducesTypeSome L (g⁻¹ * z * g) 6 1 4 1

@[expose] def Asc82Lemma74 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec7Ctx G t L S z →
    IsConj t (t * z) ∨
      ∀ s : G, IsConj t s → s ∈ centralizer ({t} : Set G) → s ≠ t →
        ∃ α : ℤˣ, InducesTypeSome L s 6 1 1 α

@[expose] def Asc82Lemma75a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec7Ctx G t L S z →
    ∃ B₁ B₂ : Subgroup G, B₁ ≠ B₂ ∧ IsNormalE16In (S ⊓ L) B₁ ∧ IsNormalE16In (S ⊓ L) B₂ ∧
      ∀ B : Subgroup G, IsNormalE16In (S ⊓ L) B → B = B₁ ∨ B = B₂

@[expose] def Asc82Lemma75b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec7Ctx G t L S z →
    ∀ B : Subgroup G, IsNormalE16In (S ⊓ L) B →
      QuotEquivTo (L ⊓ normalizer (B : Set G)) B (Equiv.Perm (Fin 5)) ∧
        L ⊓ centralizer (B : Set G) = B ∧
        (∃ φ : (Fin 5 → ZMod 2) → G,
          IsPermModuleVia IsEvenVec φ B (L ⊓ normalizer (B : Set G)) ⊤) ∧
        B = Subgroup.closure (conjClassIn (L ⊓ normalizer (B : Set G)) z)

@[expose] def Asc82Lemma76 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec7Ctx G t L S z →
    zpowers t = S ⊓ centralizer (L : Set G)

@[expose] def Asc82Lemma76Choice : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec7Ctx G t L S z →
    ∃ (g : G) (B : Subgroup G), Sec7Choice G t L S z g B

end CFSG.OddStandard.SmallF3.Omega
