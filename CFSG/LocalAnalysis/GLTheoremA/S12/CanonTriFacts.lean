module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def TriD4Schur : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (J : Subgroup Γ) (lab : GLALabel),
    LabelOf J lab → lab.tag = .triD4 → Subgroup.center ↥J = ⊥

@[expose] def TriD4Rank : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (J B : Subgroup Γ) (lab : GLALabel),
    LabelOf J lab → lab.tag = .triD4 → Subgroup.center ↥J = ⊥ →
    B ≤ Subgroup.normalizer (J : Set Γ) → IsElemAbelian 3 B →
      Nat.card B ≤ 3 ^ 3 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set Γ)) ∧
        ((∀ b ∈ B, InnerOn J b) →
          Nat.card B ≤ 3 ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set Γ)))

@[expose] def TriD4Cent3 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (J K : Subgroup Γ) (b : Γ) (lab : GLALabel),
    LabelOf J lab → lab.tag = .triD4 → Odd lab.n → 3 ≤ lab.n → Subgroup.center ↥J = ⊥ →
    b ∈ Subgroup.normalizer (J : Set Γ) → b ^ 3 = 1 → b ∉ Subgroup.centralizer (J : Set Γ) →
    IsComponentOf K (J ⊓ Subgroup.centralizer ({b} : Set Γ)) →
      (¬ InnerOn J b ∧ (LabelOf K ⟨.G2, 0, lab.n⟩ ∨
        (LabelOf K ⟨.twA, 2, lab.n⟩ ∧ Subgroup.center ↥K = ⊥))) ∨
      (InnerOn J b ∧ (LabelOf K ⟨.A, 1, 3 * lab.n⟩ ∨ LabelOf K ⟨.twA, 2, lab.n⟩))

@[expose] def TriD4LemmaJ : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (J K : Subgroup Γ) (a g : Γ) (lab : GLALabel),
    LabelOf J lab → lab.tag = .triD4 → Odd lab.n → 3 ≤ lab.n → Subgroup.center ↥J = ⊥ →
    a ∈ J → a ^ 3 = 1 → a ≠ 1 →
    IsComponentOf K (J ⊓ Subgroup.centralizer ({a} : Set Γ)) → LabelOf K ⟨.twA, 2, lab.n⟩ →
    g ∈ Subgroup.normalizer (J : Set Γ) → g ^ 3 = 1 → ¬ InnerOn J g →
    g ∈ Subgroup.centralizer ({a} : Set Γ) →
      g ∈ Subgroup.centralizer (K : Set Γ) ∨ IsMulCommutative ↥(K ⊓ Subgroup.centralizer ({g} : Set Γ))

@[expose] def NoG2Comp : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (L K : Subgroup Γ) (y : Γ) (labL : GLALabel) (p : ℕ),
    p.Prime → p ≠ 2 → y ^ p = 1 → y ∈ Subgroup.normalizer (L : Set Γ) →
    y ∉ Subgroup.centralizer (L : Set Γ) → MarkedInnDiag L y labL →
    IsComponentOf K (L ⊓ Subgroup.centralizer ({y} : Set Γ)) →
      ∀ m : ℕ, ¬ LabelOf K ⟨.G2, 0, m⟩

@[expose] def L2Rank3 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (K A : Subgroup Γ) (m : ℕ),
    LabelOf K ⟨.A, 1, m⟩ → IsElemAbelian 3 A → S10.InnDiagOn 3 A K →
      Nat.card A ≤ 3 * Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set Γ))

@[expose] def U3Setup (Γ : Type) [Group Γ] [Finite Γ] (L K B : Subgroup Γ) (y : Γ) (n : ℕ) : Prop :=
  Odd n ∧ 3 ≤ n ∧ SplitInnerDiagMarking 3 B L ∧ IsElemAbelian 3 B ∧ y ∈ B ∧
    y ∉ Subgroup.centralizer (L : Set Γ) ∧
    Nat.card B = 3 ^ 3 * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set Γ)) ∧
    K = GLALayer (L ⊓ Subgroup.centralizer ({y} : Set Γ)) ∧
    IsComponentOf K (L ⊓ Subgroup.centralizer ({y} : Set Γ)) ∧ LabelOf K ⟨.twA, 2, n⟩ ∧
    B ≤ Subgroup.normalizer (K : Set Γ) ∧
    Nat.card B = 3 ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Γ)) ∧
    ∀ E U : Subgroup Γ, E ≤ L → U ≤ L → U ≠ ⊥ → IsPGroup 2 U → E ≤ Subgroup.normalizer (U : Set Γ) →
      IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3 * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set Γ))

@[expose] def U3SubcompL : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (L K B : Subgroup Γ) (y : Γ) (n : ℕ),
    U3Setup Γ L K B y n → 3 ∣ Nat.card ↥(Subgroup.center ↥K)

@[expose] def U3SubcompTorus : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (L K B : Subgroup Γ) (y : Γ) (n : ℕ),
    U3Setup Γ L K B y n → ∀ g₁ g₂ : Γ, g₁ ∈ B → g₂ ∈ B →
      g₁ ∉ B ⊓ Subgroup.centralizer (K : Set Γ) →
      g₂ ∉ (B ⊓ Subgroup.centralizer (K : Set Γ)) ⊔ Subgroup.zpowers g₁ →
        ¬ (IsSolvable ↥(K ⊓ Subgroup.centralizer ({g₁} : Set Γ)) ∧
            IsSolvable ↥(K ⊓ Subgroup.centralizer ({g₂} : Set Γ)))

structure TriFacts : Prop where
  schur : TriD4Schur
  rank : TriD4Rank
  cent : TriD4Cent3
  lemmaJ : TriD4LemmaJ
  noG2 : NoG2Comp
  l2 : L2Rank3
  u3L : U3SubcompL
  u3Torus : U3SubcompTorus

structure TriResidualFacts : Prop where
  cent : TriD4Cent3
  lemmaJ : TriD4LemmaJ
  noG2 : NoG2Comp
  u3L : U3SubcompL
  u3Torus : U3SubcompTorus

end CFSG.LocalAnalysis.GLTheoremA
