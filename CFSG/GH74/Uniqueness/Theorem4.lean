module

public import CFSG.GH74.Uniqueness.Theorem4Basic
public import CFSG.GH74.Uniqueness.Section7Prop71
public import CFSG.GH74.Uniqueness.Section6Lemma61Triples
public import CFSG.GH74.Uniqueness.Section6Prop63
public import CFSG.GH74.Uniqueness.Section7Prop72
public import CFSG.GH74.Uniqueness.Section7Prop78
public import CFSG.GH74.Uniqueness.Section7Lemma73
public import CFSG.GH74.Uniqueness.Section7SevenD
public import CFSG.GH74.Uniqueness.Section7Lemma710
public import CFSG.GH74.Uniqueness.Section7Lemma711
public import CFSG.GH74.Uniqueness.Theorem4Cor5
public import CFSG.GH74.Uniqueness.Section7Cor712
public import CFSG.GH74.Uniqueness.Section7Cor714

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.corollary64
    (S : ZDSetup X Z M) : Cor64Stmt Z M :=
  S.cor64 S.theorem2

theorem ZDSetup.prop71
    (S : ZDSetup X Z M) : Prop71Stmt Z M := by
  have h57 := S.cor57
  have h64 := S.corollary64
  have h73 := S.lemma73 h57
  have h72 := S.prop72 h73 h64
  have h78 := S.prop78 h57 h72 h64
  have h79 := S.prop79 h72 h64
  exact prop71_of_stage2 S.invariant (S.stage2Exists h72 h78 h79 h73 S.sevenD) S.lemma710
    S.lemma711 h64

theorem ZDSetup.theorem4
    (S : ZDSetup X Z M) : Theorem4Stmt Z M :=
  S.theorem4_of_prop71 S.cor57 S.prop71

theorem ZDSetup.corollary3
    (S : ZDSetup X Z M) : Cor3Stmt Z M :=
  S.cor3 S.cor57 (S.prop63 S.theorem2)

theorem ZDSetup.lemma61b (S : ZDSetup X Z M) : Lemma61bStmt Z M :=
  lemma61b_of_lemma61a S.lemma61a

theorem ZDSetup.corollary5
    (S : ZDSetup X Z M) : Cor5Stmt Z M :=
  S.cor5 S.theorem4 S.lemma61a

theorem ZDSetup.corollary712
    (S : ZDSetup X Z M) :
    ∀ β ∈ omega M, β ≠ M → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Subgroup X,
      ABGLocalTools.IsSylowOf p P (M ⊓ β) →
      ((omegaFix M (P : Set X)).ncard = 2 → ABGLocalTools.IsSylowOf p P ⊤) ∧
      (3 ≤ (omegaFix M (P : Set X)).ncard →
        zNumShare Z M p = 1 ∧ ∃ y ∈ Z, y ∈ M ∧ y ∈ centralizer (P : Set X)) ∧
      (p ∣ zNum Z M → (omegaFix M (P : Set X)).ncard = 2 ∧ ABGLocalTools.IsSylowOf p P ⊤) :=
  fun _ hβ hβM _ hp hp2 _ hP => S.cor712 S.theorem4 S.prop52 hβ hβM hp hp2 hP

theorem ZDSetup.corollary713
    (S : ZDSetup X Z M) : Cor713Stmt Z M :=
  S.cor713 S.theorem4

theorem ZDSetup.corollary713Extra
    (S : ZDSetup X Z M) : Cor713Extra Z M :=
  S.cor713Extra S.theorem4

theorem ZDSetup.corollary714
    (S : ZDSetup X Z M) {v₁ v₂ : X} (h₁ : orderOf v₁ = 2)
    (h₂ : orderOf v₂ = 2) (hv₁ : v₁ ∈ M) (hv₂ : v₂ ∈ M)
    (hc₁ : ¬ centralizer ({v₁} : Set X) ≤ M) (hc₂ : ¬ centralizer ({v₂} : Set X) ≤ M) :
    (¬ zHull Z (centralizer ({v₁} : Set X)) ≤ M ∧ ¬ zHull Z (centralizer ({v₂} : Set X)) ≤ M) ∧
      (Group.IsSolvable ↥(zHull Z (centralizer ({v₁} : Set X))) ↔
        Group.IsSolvable ↥(zHull Z (centralizer ({v₂} : Set X)))) :=
  S.cor714 S.theorem4 h₁ h₂ hv₁ hv₂ hc₁ hc₂

end CFSG.GH74.Uniqueness
