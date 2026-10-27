module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def I133At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (X J I D : Subgroup G), GLAPComponent p X J → IsChevSimple 2 (PSimple p J) → I ≤ J →
    D ≤ Subgroup.normalizer (J : Set G) → IsPGroup p D → D ≤ cs I → card2 p J ≤ 2 * card2 p I →
    ∀ d ∈ D, CentMod p J d

@[expose] def I148DownAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X J I : Subgroup G) (d : G), GLAPComponent 3 X J → IsChevSimple 2 (PSimple 3 J) → IsTD4 3 J →
    d ∈ Subgroup.normalizer (J : Set G) → d ^ 3 = 1 → ¬ CentMod 3 J d → GLAPComponent 3 (J ⊓ cx d) I →
    Nat.sqrt (card2 3 J) ≤ 2 * card2 3 I → NonInner 3 d J ∧ IsG2Quot 3 I

@[expose] def FieldU48At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L I : Subgroup G) (d : G), GLAPComponent 3 X L → catalogIs (PSimple 3 L) S9.isU4eight →
    d ∈ Subgroup.normalizer (L : Set G) → d ^ 3 = 1 → GLAPComponent 3 (L ⊓ cx d) I →
    catalogIs (PSimple 3 I) S9.isU4two → FieldOn 3 d L

end CFSG.LocalAnalysis.GLTheoremA
