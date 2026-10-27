module

public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

@[expose] def isD4n (n : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun | .D 4 q => q.p = 2 ∧ q.exponent = n | _ => False

@[expose] def T1428NormFact : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω →
    ∀ B K : Subgroup Ω, GLAIsBmax p B → GLAPComponent p ⊤ K →
      ¬ B ≤ Subgroup.normalizer (K : Set Ω) → IsExcType p K

@[expose] def T1428TypeFact : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω →
    ∀ B L : Subgroup Ω, IsElemAbelian p B → GLATwoLocalRank p Ω ≤ CFSG.Open.pRank p B →
      GLAPComponent p ⊤ L → ¬ B ≤ Subgroup.normalizer (L : Set Ω) →
      p = 3 ∧ catalogIs (PSimple p L) weakExcIndex

@[expose] def T1428NonInnFact : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω →
    ∀ (K : Subgroup Ω) (y : Ω), GLAPComponent p ⊤ K → IsChevSimple 2 (PSimple p K) → y ^ p = 1 →
      S10.NonInnDiag p y K → ∀ J₁ J₂ : Subgroup Ω,
        GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set Ω)) J₁ →
        GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set Ω)) J₂ → J₁ = J₂

@[expose] def T1428FieldFact : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω →
    ∀ (K : Subgroup Ω) (y : Ω), GLAPComponent p ⊤ K → IsChevSimple 2 (PSimple p K) → y ^ p = 1 →
      y ∈ Subgroup.normalizer (K : Set Ω) → S10.InnDiagOn p (Subgroup.zpowers y) K →
      GLAMarking (PQuot p K) (fun lab _ _ _ _ _ => p ∣ lab.n) →
      ∀ J : Subgroup Ω, GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set Ω)) J →
        GLAMarking (PQuot p J) (fun _ _ _ _ _ _ => True) →
        GLAMarking (PQuot p J) (fun lab _ _ _ _ _ => p ∣ lab.n)

@[expose] def T1428ChevFact : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω →
    ∀ (K : Subgroup Ω) (y : Ω), GLAPComponent 3 ⊤ K → y ^ 3 = 1 →
      y ∈ Subgroup.normalizer (K : Set Ω) → IsChevSimple 2 (PSimple 3 K) →
      ∀ J : Subgroup Ω, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set Ω)) J →
        IsChevSimple 2 (PSimple 3 J)

@[expose] def T1428ExcFact : Prop :=
  ∀ (H : Type) [Group H], catalogIs (H ⧸ Subgroup.center H) excIndex →
    IsChevSimple 2 (H ⧸ Subgroup.center H) → ¬ GLAMarking H (fun lab _ _ _ _ _ => 3 ∣ lab.n)

@[expose] def T1428Config (Ω : Type) [Group Ω] [Finite Ω] (K B : Subgroup Ω) (y : Ω)
    (J₁ J₂ J₃ : Subgroup Ω) (r : ℕ) : Prop :=
  CFSG.Open.IsKGroup Ω ∧ GLAIsBmax 3 B ∧ GLAPComponent 3 ⊤ K ∧
    IsChevSimple 2 (PSimple 3 K) ∧ GLAMarking (PQuot 3 K) (fun lab _ _ _ _ _ => 3 ∣ lab.n) ∧
    y ∈ B ∧ y ≠ 1 ∧ S10.InnDiagOn 3 (Subgroup.zpowers y) K ∧ Odd r ∧ 1 < r ∧
    J₁ ≠ J₂ ∧ J₁ ≠ J₃ ∧ J₂ ≠ J₃ ∧
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set Ω)) J₁ ∧
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set Ω)) J₂ ∧
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set Ω)) J₃ ∧
    catalogIs (PSimple 3 J₁) (S10.isL2n r) ∧ catalogIs (PSimple 3 J₂) (S10.isL2n r) ∧
    catalogIs (PSimple 3 J₃) (S10.isL2n r)

@[expose] def T1428U6Fact : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (K B : Subgroup Ω) (y : Ω) (J₁ J₂ J₃ : Subgroup Ω) (r : ℕ),
    T1428Config Ω K B y J₁ J₂ J₃ r → ¬ B ≤ Subgroup.normalizer (J₁ : Set Ω) →
    (catalogIs (PSimple 3 K) (S10.isU6n r) ∧
      ∀ M : Subgroup Ω, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set Ω)) M →
        catalogIs (PSimple 3 M) (S10.isL2n r)) ∨
    catalogIs (PSimple 3 K) (isD4n r)

@[expose] def T1428D4Fact : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (K B : Subgroup Ω) (y : Ω) (J₁ J₂ J₃ : Subgroup Ω) (r : ℕ),
    T1428Config Ω K B y J₁ J₂ J₃ r → catalogIs (PSimple 3 K) (isD4n r) →
    B ≤ Subgroup.normalizer (J₁ : Set Ω)

end CFSG.LocalAnalysis.GLTheoremA.T1428

end
