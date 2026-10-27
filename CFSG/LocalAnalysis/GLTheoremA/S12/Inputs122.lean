module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Lemma121
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma102
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def isA8 : TauCeti.CFSGIndex → Prop
  | .alternating n _ => n = 8
  | _ => False

@[expose] def isG2der : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA 2 q => q.card = 3 | _ => False

@[expose] def isD4any : TauCeti.CFSGIndex → Prop :=
  onLie fun | .D 4 q => q.p = 2 | _ => False

@[expose] def l3u3Index : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .A 2 q => q.p = 2 ∧ (q.exponent % 6 = 2 ∨ q.exponent % 6 = 4)
    | .twistedA 2 q => q.p = 2 ∧ (q.exponent % 6 = 1 ∨ q.exponent % 6 = 5)
    | _ => False

@[expose] def diag2Index (i : TauCeti.CFSGIndex) : Prop := l3u3Index i ∨ S10.isA6 i

@[expose] def I112DiagAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (X B M K : Subgroup G) (b : G), p.Prime → p ≠ 2 → CFSG.Open.IsKGroup ↥X → IsElemAbelian p B → B ≤ X →
    GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B → GLAPComponent p X M → b ∈ B →
    b ∉ Subgroup.normalizer (M : Set G) →
    GLAPComponent p (closureIn M B ⊓ Subgroup.centralizer ({b} : Set G)) K → IsChevSimple 2 (PSimple p K) →
    InnDiagOn p B K → p ^ 2 * Nat.card ↥(B ⊓ centModSubgroup p K) ≤ Nat.card B →
    p = 3 ∧ catalogIs (PSimple 3 K) diag2Index ∧ Subgroup.center (PQuot 3 K) = ⊥

@[expose] def I1419FourAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L K : Subgroup G) (y : G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X L → y ∈ Subgroup.normalizer (L : Set G) → y ^ 3 = 1 →
    ¬ CentMod 3 L y → GLAPComponent 3 (L ⊓ Subgroup.centralizer ({y} : Set G)) K →
    catalogIs (PSimple 3 K) l3u3Index → Subgroup.center (PQuot 3 K) = ⊥ → ¬ InnDiagOn 3 (Subgroup.zpowers y) L

@[expose] def I1416TwoAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (X J K A : Subgroup G) (y : G), p.Prime → p ≠ 2 → CFSG.Open.IsKGroup ↥X → GLAPComponent p X J →
    y ∈ Subgroup.normalizer (J : Set G) → y ^ p = 1 → ¬ CentMod p J y →
    GLAPComponent p (J ⊓ Subgroup.centralizer ({y} : Set G)) K → IsChevSimple 2 (PSimple p K) →
    IsElemAbelian p A → InnDiagOn p A K → p ^ 2 * Nat.card ↥(A ⊓ centModSubgroup p K) ≤ Nat.card A →
    IsChevSimple 2 (PSimple p J) ∨
      (p = 3 ∧ catalogIs (PSimple 3 K) (fun i => S10.isA6 i ∨ isA8 i ∨ isG2der i ∨ S9.isU4two i))

@[expose] def I141DynkinAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (X L K A : Subgroup G) (y : G), p.Prime → p ≠ 2 → GLAPComponent p X L → IsChevSimple 2 (PSimple p L) →
    IsElemAbelian p A → A ≤ Subgroup.normalizer (L : Set G) → InnDiagOn p A L →
    p ^ 3 * Nat.card ↥(A ⊓ centModSubgroup p L) ≤ Nat.card A → y ∈ A → ¬ CentMod p L y →
    GLAPComponent p (L ⊓ Subgroup.centralizer ({y} : Set G)) K → ¬ catalogIs (PSimple p K) isG2der

@[expose] def I1429At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X J K : Subgroup G) (y : G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X J → IsChevSimple 3 (PSimple 3 J) →
    y ∈ Subgroup.normalizer (J : Set G) → y ^ 3 = 1 → ¬ CentMod 3 J y →
    GLAPComponent 3 (J ⊓ Subgroup.centralizer ({y} : Set G)) K → catalogIs (PSimple 3 K) S9.isU4two →
    6 ≤ GLATwoLocalRank 3 (PQuot 3 J)

@[expose] def I102InnAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L A : Subgroup G), GLAPComponent 3 X L →
    catalogIs (PSimple 3 L) (fun i => S9.isD4two i ∨ S9.isU5two i ∨ S9.isU6two i) → IsElemAbelian 3 A →
    A ≤ Subgroup.normalizer (L : Set G) → (∀ a ∈ A, InducesInnerMod 3 L a) →
    Nat.card A ≤ 3 ^ 4 * Nat.card ↥(A ⊓ centModSubgroup 3 L)

@[expose] def A8CatAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (B : Subgroup G) (x : G) (L D K : Subgroup G), IsSStarMax 3 B x L → 3 ^ 4 ≤ Nat.card B →
    GLAStdSubPre 3 B x L D K → catalogIs (PSimple 3 K) isA8 →
    (∃ T : Subgroup G, T ≤ K ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      (⁅T, B⁆ : Subgroup G) ≠ ⊥ ∧ 8 < Nat.card T ∧ ¬ T ≤ GLAPPrimeCoreOf 3 K) ∧
    ∃ E : Subgroup G, IsE3 3 B E ∧ D ≤ E ∧ GLAPLayer 3 (K ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥

@[expose] def U42CatAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (B : Subgroup G) (x : G) (L D K : Subgroup G), IsSStarMax 3 B x L → 3 ^ 4 ≤ Nat.card B →
    catalogIs (PSimple 3 L) (fun i => S9.isD4two i ∨ S9.isU5two i ∨ S9.isU6two i) →
    (∀ b ∈ B, InducesInnerMod 3 L b) → GLAStdSubPre 3 B x L D K → catalogIs (PSimple 3 K) S9.isU4two →
    (∃ T₀ : Subgroup G, T₀ ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 2 T₀ ∧
      B ≤ Subgroup.normalizer (T₀ : Set G) ∧ (⁅T₀, B⁆ : Subgroup G) ≠ ⊥ ∧
      ¬ T₀ ≤ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G))) →
    ∃ T : Subgroup G, T ≤ K ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      (⁅T, B⁆ : Subgroup G) ≠ ⊥ ∧ 8 < Nat.card T ∧ ¬ T ≤ GLAPPrimeCoreOf 3 K

@[expose] def TriHalfSplitAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X J : Subgroup G), GLAPComponent 3 X J → CFSG.Open.IsQuasisimple ↥J → IsChevSimple 2 (PSimple 3 J) →
    (catalogIs (PSimple 3 J) isD4any ∨ IsTD4 3 J) →
    ∃ lab : GLALabel, LabelOf J lab ∧ (lab.tag = .D ∨ lab.tag = .triD4) ∧
      GLAHalfSplit16 3 lab (Subgroup.center ↥J = ⊥)

@[expose] def I91FieldAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (X J : Subgroup G) (b : G), GLAPComponent p X J → IsChevSimple 2 (PSimple p J) →
    b ∈ Subgroup.normalizer (J : Set G) → b ^ p = 1 → NonInnDiag p b J →
    FieldOn p b J ∨ (p = 3 ∧ (catalogIs (PSimple 3 J) isD4any ∨ IsTD4 3 J))

@[expose] def SmallDisjointAt : Prop :=
  ∀ (S : Type) [Group S], catalogIs S S9.isU4two → ¬ catalogIs S S10.isA6

structure Inputs122 (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  l121 : Inputs121 G p
  l102 : Lemma102Inputs G p
  i112 : I112DiagAt G
  i1419 : I1419FourAt G
  i1416 : I1416TwoAt G
  i141 : I141DynkinAt G
  i1429 : I1429At G
  i102 : I102InnAt G
  a8 : A8CatAt G
  u42 : U42CatAt G
  trihalf : TriHalfSplitAt G
  i91 : I91FieldAt G p
  disj : SmallDisjointAt

end CFSG.LocalAnalysis.GLTheoremA
