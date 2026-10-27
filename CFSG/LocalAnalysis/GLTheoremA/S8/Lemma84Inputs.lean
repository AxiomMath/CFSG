module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S6.AltDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

namespace S8.L84

variable {G : Type} [Group G]

@[expose] def isType1430 (i : TauCeti.CFSGIndex) : Prop :=
  isAltN 9 i ∨ sporIs .J3 i ∨
    onLie (fun
      | .B 3 q => q.card = 2
      | .A 1 q => q.card = 729
      | .B 2 q => q.card = 8
      | _ => False) i

@[expose] def isSp48 : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .B 2 q => q.card = 8
    | _ => False

@[expose] def isSp82 : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .B 4 q => q.card = 2
    | _ => False

@[expose] def UniqA6 [Finite G] (Y : Subgroup G) : Prop :=
  ∃ I : Subgroup G, GLAPComponent 3 Y I ∧ (∀ I' : Subgroup G, GLAPComponent 3 Y I' → I' = I) ∧
    IsTypeWithCenter 3 I isA6 1 ∧ Nat.card (PQuot 3 I) = 360

@[expose] def T1430 [Finite G] (J E : Subgroup G) : Prop :=
  catalogIs (PSimple 3 J) isType1430 ∧
    (catalogIs (PSimple 3 J) isSp48 → ∃ e ∈ E, ¬ InducesInnerMod 3 J e)

@[expose] def SpA12Type [Finite G] (K : Subgroup G) : Prop :=
  (catalogIs (PSimple 3 K) isSp82 ∨ catalogIs (PSimple 3 K) (isAltN 12)) ∧
    Nat.card (Subgroup.center (PQuot 3 K)) = 1

@[expose] def I1016ONAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (X L : Subgroup G), GLAPComponent p X L →
    catalogIs (PSimple p L) (sporIs .ONan) →
    ∀ E T : Subgroup G, E ≤ L → IsElemAbelian p E → T ≤ L → IsPGroup 2 T →
      ¬ T ≤ GLAPPrimeCoreOf p L → E ≤ Subgroup.normalizer (T : Set G) →
      (p = 3 ∧ Nat.card E ≤ 3 ^ 3) ∨ Nat.card E ≤ p

@[expose] def I1425At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L : Subgroup G), GLAPComponent 3 X L → IsTypeWithCenter 3 L (sporIs .ONan) 1 →
    ∀ F : Subgroup G, F ≤ L → IsElemAbelian 3 F → Nat.card F = 3 ^ 3 →
    ∃ D₀ : Subgroup G, D₀ ≤ F ∧ Nat.card D₀ = 3 ^ 2 ∧
      UniqA6 (L ⊓ Subgroup.centralizer (D₀ : Set G)) ∧
      ∀ d ∈ D₀, d ≠ 1 → UniqA6 (L ⊓ cx d)

@[expose] def I112At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X B L₁ : Subgroup G), CFSG.Open.IsKGroup ↥X → B ≤ X → IsElemAbelian 3 B →
    (∀ W U : Subgroup G, W ≤ X → IsElemAbelian 3 W → U ≤ X → U ≠ ⊥ → IsPGroup 2 U →
      W ≤ Subgroup.normalizer (U : Set G) → Nat.card W ≤ Nat.card B) →
    GLAPComponent 3 X L₁ → ¬ B ≤ Subgroup.normalizer (L₁ : Set G) →
    ¬ IsTypeWithCenter 3 L₁ isA6 1 ∧ ¬ catalogIs (PSimple 3 L₁) isType1430 ∧
      (∀ W : Subgroup G, W ≤ L₁ → IsElemAbelian 3 W → Nat.card W ≤ 3 ^ 2) ∧
      ∀ b ∈ B, b ∉ Subgroup.normalizer (L₁ : Set G) → ∀ J : Subgroup G,
        GLAPComponent 3 (closureIn L₁ B ⊓ cx b) J → Nonempty (PQuot 3 J ≃* PSimple 3 L₁)

@[expose] def A6FactsAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X J : Subgroup G), GLAPComponent 3 X J → catalogIs (PSimple 3 J) isA6 →
    (∃ y ∈ barX 3 X J, orderOf y = 3 ∧ (∃ z ∈ barX 3 X J, z * y ≠ y * z) ∧
      ∃ T : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X), T ≤ barX 3 X J ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
        y ∈ Subgroup.normalizer (T : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) ∧
    (Nat.card (Subgroup.center (PQuot 3 J)) = 1 → ∀ J₀ : Subgroup G, J₀ ≤ J →
      J₀ ⊔ GLAPPrimeCoreOf 3 J = J →
      ∃ F : Subgroup G, F ≤ J₀ ∧ IsElemAbelian 3 F ∧ Nat.card F = 3 ^ 2)

@[expose] def I1430At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X E D J I : Subgroup G), CFSG.Open.IsKGroup ↥X → E ≤ X → IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
    D ≤ E → Nat.card D = 3 ^ 2 → X ≤ Subgroup.centralizer (D : Set G) →
    GLAPComponent 3 X J → E ≤ Subgroup.normalizer (J : Set G) →
    GLAPComponent 3 (J ⊓ Subgroup.centralizer (E : Set G)) I → IsTypeWithCenter 3 I isA6 1 →
    ¬ J ≤ I ⊔ GLAPPrimeCoreOf 3 J → GLATwoLocalRank 3 G ≤ 4 → T1430 J E

@[expose] def I106T1430At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X J : Subgroup G), GLAPComponent 3 X J → catalogIs (PSimple 3 J) isType1430 →
    (¬ catalogIs (PSimple 3 J) isSp48 → ∃ F : Subgroup G, F ≤ J ∧ IsElemAbelian 3 F ∧
      Nat.card F = 3 ^ 3 ∧ ∀ f ∈ F, CentMod 3 J f → f = 1) ∧
    (catalogIs (PSimple 3 J) isSp48 → ∀ y : G, y ∈ Subgroup.normalizer (J : Set G) → y ^ 3 = 1 →
      ¬ InducesInnerMod 3 J y → ∃ F : Subgroup G, F ≤ J ⊓ cx y ∧ IsElemAbelian 3 F ∧
        Nat.card F = 3 ^ 2 ∧ ∀ f ∈ F, CentMod 3 J f → f = 1)

@[expose] def I1431At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X B K J : Subgroup G) (d y : G), CFSG.Open.IsKGroup ↥X → B ≤ X → IsElemAbelian 3 B →
    GLATwoLocalRank 3 G ≤ 4 → GLAPComponent 3 X K → B ≤ Subgroup.normalizer (K : Set G) →
    (∃ c ∈ B, c ≠ 1 ∧ CentMod 3 K c) → d ∈ B → GLAPComponent 3 (K ⊓ cx d) J → T1430 J B →
    ¬ K ≤ J ⊔ GLAPPrimeCoreOf 3 K → y ∈ B →
    (∃ Ia : Subgroup G, GLAPComponent 3 (K ⊓ cx y) Ia ∧ IsTypeWithCenter 3 Ia isA6 1) →
    SpA12Type K

@[expose] def KFactsAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K : Subgroup G), GLAPComponent 3 X K → SpA12Type K →
    ¬ catalogIs (PSimple 3 K) (sporIs .ONan) ∧
    (∀ W : Subgroup G, W ≤ K → IsElemAbelian 3 W → Nat.card W ≤ 3 ^ 4) ∧
    (∀ K₀ : Subgroup G, K₀ ≤ K → K₀ ⊔ GLAPPrimeCoreOf 3 K = K → ∃ F T : Subgroup G, F ≤ K₀ ∧
      IsElemAbelian 3 F ∧ Nat.card F = 3 ^ 3 ∧ T ≤ K ∧ IsPGroup 2 T ∧ ¬ T ≤ GLAPPrimeCoreOf 3 K ∧
      F ≤ Subgroup.normalizer (T : Set G)) ∧
    (∀ g ∈ Subgroup.normalizer (K : Set G), (∃ k : ℕ, g ^ (3 ^ k) = 1) → InducesInnerMod 3 K g) ∧
    ∀ F : Subgroup G, F ≤ K → IsElemAbelian 3 F → Nat.card F = 3 ^ 4 →
      (∃ n ∈ K, n ∈ Subgroup.normalizer (F : Set G) ∧ (∃ k : ℕ, n ^ (3 ^ k) = 1) ∧
        n ∉ Subgroup.centralizer (F : Set G)) ∧
      ∀ Q : Subgroup G, IsPGroup 3 Q → Q ≤ Subgroup.normalizer (K : Set G) →
        Q ≤ Subgroup.normalizer (F : Set G) → (Subgroup.centralizer (F : Set G)).relIndex Q ≤ 3

@[expose] def ONFactsAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L : Subgroup G), GLAPComponent 3 X L → IsTypeWithCenter 3 L (sporIs .ONan) 1 →
    (∀ Q : Subgroup G, Q ≤ L → IsPGroup 3 Q →
      ∃ H : Subgroup G, Q ≤ H ∧ H ≤ L ∧ IsElemAbelian 3 H ∧ Nat.card H = 3 ^ 4) ∧
    ∀ H : Subgroup G, H ≤ L → IsElemAbelian 3 H → Nat.card H = 3 ^ 4 →
      (∀ h ∈ H, h ≠ 1 → ∀ h' ∈ H, h' ≠ 1 →
        ∃ n ∈ L, n ∈ Subgroup.normalizer (H : Set G) ∧ n * h * n⁻¹ = h') ∧
      ∀ g ∈ Subgroup.normalizer (L : Set G), g ∈ Subgroup.normalizer (H : Set G) →
        (∃ k : ℕ, g ^ (3 ^ k) = 1) → g ∈ Subgroup.centralizer (H : Set G)

end S8.L84

end CFSG.LocalAnalysis.GLTheoremA
