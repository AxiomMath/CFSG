module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Compl123
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def I167Field : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (p : ℕ) (B X D J : Subgroup Ω) (x : Ω),
    p.Prime → p ≠ 2 → IsElemAbelian p B →
    CFSG.Open.IsQuasisimple ↥X → IsChevSimple 2 (PSimple p X) →
    B ≤ Subgroup.normalizer (X : Set Ω) →
    GLATwoLocalRank p ↥(X ⊔ B) ≤ CFSG.Open.pRank p B →
    (∀ g ∈ X ⊔ B, g ∈ Subgroup.centralizer (B : Set Ω) → orderOf g = p → g ∈ B) →
    Nat.card ↥(B ⊓ cs X) = p → IsE2 p B D → GLAPComponent p (X ⊓ cs D) J → D = B ⊓ cs J →
    Type167J p J → (HalfSplit16At p X ∨ ∃ d ∈ D, FieldOn p d X) →
    x ∈ D → x ∉ cs X → D = (B ⊓ cs X) ⊔ Subgroup.zpowers x →
    FieldOn p x X → Type167 p X J

@[expose] def I167Tri : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (p : ℕ) (B X D J : Subgroup Ω) (x : Ω),
    p.Prime → p ≠ 2 → IsElemAbelian p B →
    CFSG.Open.IsQuasisimple ↥X → IsChevSimple 2 (PSimple p X) →
    B ≤ Subgroup.normalizer (X : Set Ω) →
    GLATwoLocalRank p ↥(X ⊔ B) ≤ CFSG.Open.pRank p B →
    (∀ g ∈ X ⊔ B, g ∈ Subgroup.centralizer (B : Set Ω) → orderOf g = p → g ∈ B) →
    Nat.card ↥(B ⊓ cs X) = p → IsE2 p B D → GLAPComponent p (X ⊓ cs D) J → D = B ⊓ cs J →
    Type167J p J → (HalfSplit16At p X ∨ ∃ d ∈ D, FieldOn p d X) →
    x ∈ D → x ∉ cs X → D = (B ⊓ cs X) ⊔ Subgroup.zpowers x →
    (∀ d ∈ D, ¬ FieldOn p d X) → NonInnDiag p x X → p = 3 →
    (catalogIs (PSimple 3 X) isD4any ∨ IsTD4 3 X) → False

@[expose] def I167Class : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (p : ℕ) (B X D J : Subgroup Ω) (x : Ω),
    p.Prime → p ≠ 2 → IsElemAbelian p B →
    CFSG.Open.IsQuasisimple ↥X → IsChevSimple 2 (PSimple p X) →
    B ≤ Subgroup.normalizer (X : Set Ω) →
    GLATwoLocalRank p ↥(X ⊔ B) ≤ CFSG.Open.pRank p B →
    (∀ g ∈ X ⊔ B, g ∈ Subgroup.centralizer (B : Set Ω) → orderOf g = p → g ∈ B) →
    Nat.card ↥(B ⊓ cs X) = p → IsE2 p B D → GLAPComponent p (X ⊓ cs D) J → D = B ⊓ cs J →
    Type167J p J → (HalfSplit16At p X ∨ ∃ d ∈ D, FieldOn p d X) →
    x ∈ D → x ∉ cs X → D = (B ⊓ cs X) ⊔ Subgroup.zpowers x →
    (∀ d ∈ D, ¬ FieldOn p d X) → HalfSplit16At p X → InnDiagOn p (Subgroup.zpowers x) X →
    catalogIs (PSimple p X) K1419.I1419Classical2 → Type167 p X J

@[expose] def I167Exc3 : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (p : ℕ) (B X D J : Subgroup Ω) (x : Ω),
    p.Prime → p ≠ 2 → IsElemAbelian p B →
    CFSG.Open.IsQuasisimple ↥X → IsChevSimple 2 (PSimple p X) →
    B ≤ Subgroup.normalizer (X : Set Ω) →
    GLATwoLocalRank p ↥(X ⊔ B) ≤ CFSG.Open.pRank p B →
    (∀ g ∈ X ⊔ B, g ∈ Subgroup.centralizer (B : Set Ω) → orderOf g = p → g ∈ B) →
    Nat.card ↥(B ⊓ cs X) = p → IsE2 p B D → GLAPComponent p (X ⊓ cs D) J → D = B ⊓ cs J →
    Type167J p J → (HalfSplit16At p X ∨ ∃ d ∈ D, FieldOn p d X) →
    x ∈ D → x ∉ cs X → D = (B ⊓ cs X) ⊔ Subgroup.zpowers x →
    (∀ d ∈ D, ¬ FieldOn p d X) → HalfSplit16At p X → InnDiagOn p (Subgroup.zpowers x) X →
    ¬ catalogIs (PSimple p X) K1419.I1419Classical2 → p = 3 → False

@[expose] def I167Exc : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (p : ℕ) (B X D J : Subgroup Ω) (x : Ω),
    p.Prime → p ≠ 2 → IsElemAbelian p B →
    CFSG.Open.IsQuasisimple ↥X → IsChevSimple 2 (PSimple p X) →
    B ≤ Subgroup.normalizer (X : Set Ω) →
    GLATwoLocalRank p ↥(X ⊔ B) ≤ CFSG.Open.pRank p B →
    (∀ g ∈ X ⊔ B, g ∈ Subgroup.centralizer (B : Set Ω) → orderOf g = p → g ∈ B) →
    Nat.card ↥(B ⊓ cs X) = p → IsE2 p B D → GLAPComponent p (X ⊓ cs D) J → D = B ⊓ cs J →
    Type167J p J → (HalfSplit16At p X ∨ ∃ d ∈ D, FieldOn p d X) →
    x ∈ D → x ∉ cs X → D = (B ⊓ cs X) ⊔ Subgroup.zpowers x →
    (∀ d ∈ D, ¬ FieldOn p d X) → HalfSplit16At p X → InnDiagOn p (Subgroup.zpowers x) X →
    ¬ catalogIs (PSimple p X) K1419.I1419Classical2 → p ≠ 3 → False

end CFSG.LocalAnalysis.GLTheoremA.I167

end
