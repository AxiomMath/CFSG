module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def T171ShapeFact : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (B : Subgroup Ω) (x : Ω) (L D K : Subgroup Ω) (β : Ω),
    CFSG.Open.IsKGroup Ω → S171.Cfg Ω p B x L → S171.MaxG p B → L.Normal →
    GLAStdSubPre p B x L D K → GLAPComponent p (L ⊓ Subgroup.centralizer (D : Set Ω)) K →
    IsChevSimple 2 (PSimple p K) → β ∈ B → β ∉ D → ¬ InnDiagOn p (Subgroup.zpowers β) K →
    S171.ExtremalType p L

@[expose] def T171SizeFact : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (B : Subgroup Ω) (x : Ω) (L D K : Subgroup Ω) (β : Ω),
    CFSG.Open.IsKGroup Ω → S171.Cfg Ω p B x L → L.Normal →
    GLAStdSubPre p B x L D K → GLAPComponent p (L ⊓ Subgroup.centralizer (D : Set Ω)) K →
    IsChevSimple 2 (PSimple p K) → β ∈ B → β ∉ D → ¬ InnDiagOn p (Subgroup.zpowers β) K →
    S171.ExtremalType p L →
    (∀ n : ℕ, catalogIs (PSimple p L) (S10.isU6n n) → Nat.card B ≤ 3 ^ 4) ∧
      (∀ n : ℕ, catalogIs (PSimple p L) (S10.isTE6n n) → Nat.card B ≤ 3 ^ 5)

@[expose] def T171NoActFact : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (B : Subgroup Ω) (x : Ω) (L D K : Subgroup Ω) (β : Ω),
    CFSG.Open.IsKGroup Ω → S171.Cfg Ω p B x L → S171.MaxG p B → L.Normal →
    GLAStdSubPre p B x L D K → GLAPComponent p (L ⊓ Subgroup.centralizer (D : Set Ω)) K →
    IsChevSimple 2 (PSimple p K) → β ∈ B → β ∉ D → ¬ InnDiagOn p (Subgroup.zpowers β) K →
    S171.ExtremalType p L →
    ∀ T : Subgroup Ω, T ≤ Subgroup.normalizer (L : Set Ω) → T ≤ Subgroup.centralizer ({x} : Set Ω) →
      IsPGroup 2 T → B ≤ Subgroup.normalizer (T : Set Ω) →
      (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (L : Set Ω)

@[expose] def T171SmallTypeFact : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (B : Subgroup Ω) (x : Ω) (L : Subgroup Ω),
    CFSG.Open.IsKGroup Ω → S171.Cfg Ω 3 B x L → L.Normal → S171.MaxG 3 B →
    (∃ D K : Subgroup Ω, GLAStdSubPre 3 B x L D K) →
    (∀ D K : Subgroup Ω, GLAStdSubPre 3 B x L D K → GLASmall K) →
    (∃ T : Subgroup Ω, T ≤ Subgroup.normalizer (L : Set Ω) ∧ T ≤ Subgroup.centralizer ({x} : Set Ω) ∧
      IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set Ω) ∧ (⁅T, B⁆ : Subgroup Ω) ≠ ⊥) →
    catalogIs (↥L ⧸ Subgroup.center ↥L) (fun i => S9.isU5two i ∨ S9.isU6two i ∨ S9.isD4two i)

@[expose] def T171InnerU6Fact : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (B : Subgroup Ω) (x : Ω) (L : Subgroup Ω),
    CFSG.Open.IsKGroup Ω → S171.Cfg Ω 3 B x L → L.Normal → S171.MaxG 3 B →
    (∃ D K : Subgroup Ω, GLAStdSubPre 3 B x L D K) →
    (∀ D K : Subgroup Ω, GLAStdSubPre 3 B x L D K → GLASmall K) →
    (∃ T : Subgroup Ω, T ≤ Subgroup.normalizer (L : Set Ω) ∧ T ≤ Subgroup.centralizer ({x} : Set Ω) ∧
      IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set Ω) ∧ (⁅T, B⁆ : Subgroup Ω) ≠ ⊥) →
    catalogIs (↥L ⧸ Subgroup.center ↥L) S9.isU6two → ∀ b ∈ B, InducesInnerMod 3 L b

end CFSG.LocalAnalysis.GLTheoremA.T171

end
