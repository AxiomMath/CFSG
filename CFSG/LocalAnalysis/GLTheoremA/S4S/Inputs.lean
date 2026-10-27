module

public import CFSG.LocalAnalysis.GLTheoremA.P55.Inputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21
public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def IsTwoPrimaryWeaklyLocallyBalanced (p k : ℕ) {K : Type*} [Group K]
    (A : Subgroup (MulAut K)) : Prop :=
  ∀ D : Subgroup (MulAut K), IsEkIn p k A D → ∀ H : Subgroup (MulAut K), innerAut K ≤ H →
    A ≤ Subgroup.normalizer (H : Set (MulAut K)) →
      Odd (Nat.card (⁅localDeltaIn p H D, A⁆ : Subgroup (MulAut K)))

@[expose] def IsCompTwoPrimaryWeaklyLocallyBalanced (p k : ℕ) {G : Type*} [Group G]
    (B L : Subgroup G) : Prop :=
  IsTwoPrimaryWeaklyLocallyBalanced p k (autBar p B L)

@[expose] def IsMaxRankIn {G : Type*} [Group G] (p : ℕ) (B Y : Subgroup G) : Prop :=
  ∀ E : Subgroup G, E ≤ Y → IsElemAbelian p E → Nat.card E ≤ Nat.card B

@[expose] def imageMod {G : Type} [Group G] (p : ℕ) (J T : Subgroup G) : Subgroup (PQuot p J) :=
  (T.subgroupOf J).map (QuotientGroup.mk' (GLAPPrimeCore p ↥J))

@[expose] def isTrialityD4Big : TauCeti.LieTypeIndex → Prop
  | .trialityD4 q => 2 < q.card ∧ ¬ 3 ∣ q.card
  | _ => False

@[expose] def isG2Big : TauCeti.LieTypeIndex → Prop
  | .G2 q => 2 < q.card ∧ ¬ 3 ∣ q.card
  | _ => False

@[expose] def isM12 : TauCeti.CFSGIndex → Prop
  | .sporadic s => s = .M12
  | _ => False

@[expose] def isSmallThree : TauCeti.CFSGIndex → Prop
  | .alternating n _ => n = 7 ∨ n = 10
  | .sporadic s => s = .M12 ∨ s = .M22
  | _ => False

@[expose] def k3NoA10 : TauCeti.CFSGIndex → Prop
  | .alternating n _ => n = 7
  | .sporadic s => s = .M12 ∨ s = .M22
  | .lie i => k3Lie i.1
  | .cyclic _ _ => False

variable {G : Type} [Group G] [Finite G]

@[expose] def I321UsedAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → ∀ A J : Subgroup G, Nat.Coprime p (Nat.card A) → J ≤ Subgroup.normalizer (A : Set G) →
    (∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → Nat.Coprime p (N.subgroupOf J).index →
      N = J) → ⁅⁅A, J⁆, J⁆ = ⁅A, J⁆

@[expose] def Input14_5Print : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ p : ℕ, p.Prime → p ≠ 2 →
    GLAPPrimeCore p X = ⊥ → ∀ P : Subgroup X, P ≠ ⊥ → IsPGroup p P →
      ⁅GLAPLayer p (Subgroup.normalizer (P : Set X)),
        GLAPPrimeCoreOf p (Subgroup.normalizer (P : Set X))⁆ = ⊥

@[expose] def I145UsedAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ X D : Subgroup G, CFSG.Open.IsKGroup ↥X → D ≤ X → IsPGroup p D →
    ⁅GLAPLayer p (X ⊓ Subgroup.centralizer (D : Set G)),
      GLAPPrimeCoreOf p (X ⊓ Subgroup.centralizer (D : Set G))⁆ ≤ GLAPPrimeCoreOf p X

@[expose] def I1810UsedAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ Y K₁ B R : Subgroup G, CFSG.Open.IsKGroup ↥Y → GLAPComponent p Y K₁ → IsPGroup p B →
    B ≤ Subgroup.normalizer (Y : Set G) → R ≠ ⊥ → IsPGroup 2 R →
    R ≤ ⁅closureIn K₁ B, GLAPPrimeCoreOf p Y⁆ →
    ¬ 2 ∣ R.relIndex ⁅closureIn K₁ B, GLAPPrimeCoreOf p Y⁆ → B ≤ Subgroup.normalizer (R : Set G) →
    closureIn K₁ B ⊓ Subgroup.centralizer (R : Set G) ≤ oPPrimeP p (closureIn K₁ B)

@[expose] def I1912At : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    p ∣ Nat.card K → (K1Cover p K ∨ K2Cover p K) →
    ∀ A : Subgroup (MulAut K), IsElemAbelian p A →
      IsTwoPrimaryWeaklyLocallyBalanced p 1 A ∨
        (p = 3 ∧ catalogIs (K ⧸ Subgroup.center K) (onLie (isL2 27)) ∧ ¬ A ≤ innerAut K)

@[expose] def I1933At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → CFSG.Open.IsKProper G →
    ∀ (B D : Subgroup G) (k : ℕ) (b : G), IsElemAbelian p B → 1 ≤ k → IsEkIn p k B D → b ∈ B →
      b ≠ 1 → (∀ J : Subgroup G, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) J →
        B ≤ Subgroup.normalizer (J : Set G) ∧ IsCompTwoPrimaryWeaklyLocallyBalanced p k B J) →
      ∀ T : Subgroup G, IsPGroup 2 T → B ≤ Subgroup.normalizer (T : Set G) →
        T ≤ GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G) →
        ⁅T, B⁆ ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G))

@[expose] def I1913At : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    catalogIs (K ⧸ Subgroup.center K) isSmallThree → ∀ H : Subgroup (MulAut K), innerAut K ≤ H →
      ∀ x ∈ H, orderOf x = 3 →
        Nat.card (GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({x} : Set (MulAut K)))) ≤ 4

@[expose] def I2027At : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    catalogIs (K ⧸ Subgroup.center K) (onLie k3Lie) → ∀ A S : Subgroup (MulAut K),
      IsPGroup 3 A → IsPGroup 2 S → A ≤ Subgroup.normalizer (S : Set (MulAut K)) →
        (⁅A, S⁆ : Subgroup (MulAut K)) = S → (⁅A, (⁅S, S⁆ : Subgroup (MulAut K))⁆ : Subgroup (MulAut K)) = ⊥

@[expose] def I264At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsElemAbelian p B → x ∈ B →
    x ≠ 1 → GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L → CFSG.Open.IsKGroup ↥L →
    B ≤ Subgroup.normalizer (L : Set G) → p ^ 4 ≤ Nat.card B → IsMaxRankIn p B (L ⊔ B) →
    fullCoverLevel p (PQuot p L) = 4 →
    IsGB p B L ∨ (p = 3 ∧ Nat.card B = 3 ^ 4 ∧ (∀ b ∈ B, CentMod 3 L b ↔ b ∈ Subgroup.zpowers x) ∧
      catalogIs (PSimple 3 L) (onLie isTrialityD4Big) ∧ ∃ b ∈ B, ¬ InducesInnerMod 3 L b)

@[expose] def I91At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L : Subgroup G) (b : G), GLAPComponent 3 X L → catalogIs (PSimple 3 L) (onLie isTrialityD4Big) →
    b ∈ Subgroup.normalizer (L : Set G) → b ^ 3 = 1 → ¬ InducesInnerMod 3 L b →
    ∃ y ∈ L ⊔ Subgroup.zpowers b, y ^ 3 = 1 ∧ ¬ InducesInnerMod 3 L y ∧
      GLAPComponent 3 (L ⊓ Subgroup.centralizer ({y} : Set G))
        (GLAPLayer 3 (L ⊓ Subgroup.centralizer ({y} : Set G))) ∧
      catalogIs (PSimple 3 (GLAPLayer 3 (L ⊓ Subgroup.centralizer ({y} : Set G))))
        (onLie isG2Big)

@[expose] def I147At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (Y L₀ : Subgroup G), GLAPComponent 3 Y L₀ → catalogIs (PSimple 3 L₀) (onLie isG2Big) →
    (∃ D : Subgroup G, D ≤ L₀ ∧ IsElemAbelian 3 D ∧ Nat.card D = 9) ∧
    (∀ z ∈ L₀, z ^ 3 = 1 → z ≠ 1 → GLAPLayer 3 (L₀ ⊓ Subgroup.centralizer ({z} : Set G)) ≠ ⊥) ∧
    Subgroup.center (PQuot 3 L₀) = ⊥

@[expose] def I1016At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L A : Subgroup G), GLAPComponent 3 X L → catalogIs (PSimple 3 L) isM12 →
    IsElemAbelian 3 A → A ≤ Subgroup.normalizer (L : Set G) → (∀ a ∈ A, CentMod 3 L a) →
    Subgroup.center (PQuot 3 L) = ⊥ ∧
    ∃ D : Subgroup G, D ≤ L ⊓ Subgroup.centralizer (A : Set G) ∧ IsElemAbelian 3 D ∧
      Nat.card D = 9 ∧ ∃ U : Subgroup G, U ≤ L ∧ IsPGroup 2 U ∧
        A ⊔ D ≤ Subgroup.normalizer (U : Set G) ∧ ¬ U ≤ GLAPPrimeCoreOf 3 L

@[expose] def I71M12At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L B : Subgroup G), GLAPComponent 3 X L → catalogIs (PSimple 3 L) isM12 →
    IsElemAbelian 3 B → B ≤ Subgroup.normalizer (L : Set G) →
    Nat.card B ≤ 9 * Nat.card (B ⊓ centModSubgroup 3 L : Subgroup G)

@[expose] def I1426At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p = 3 → ∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsElemAbelian 3 B → x ∈ B → x ≠ 1 →
    GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) L → B ≤ Subgroup.normalizer (L : Set G) →
    fullCoverLevel 3 (PQuot 3 L) = 3 → 3 ^ 4 ≤ Nat.card B → IsMaxRankIn 3 B (L ⊔ B) →
    (∀ E : Subgroup G, E ≤ B → IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      GLAPLayer 3 (L ⊓ Subgroup.centralizer (E : Set G)) = ⊥) →
    (catalogIs (PSimple 3 L) isM12 → ∃ U : Subgroup G, U ≤ L ∧ IsPGroup 2 U ∧
      B ≤ Subgroup.normalizer (U : Set G) ∧ ¬ U ≤ GLAPPrimeCoreOf 3 L) →
    Nat.card B = 3 ^ 4 ∧ ∃ A J₁ T₁ : Subgroup G, A ≤ B ∧ IsElemAbelian 3 A ∧ Nat.card A = 9 ∧
      J₁ = GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)) ∧
      GLAPComponent 3 (L ⊓ Subgroup.centralizer (A : Set G)) J₁ ∧
      catalogIs (PSimple 3 J₁) k3NoA10 ∧ (∀ b ∈ B, CentMod 3 J₁ b ↔ b ∈ A) ∧
      T₁ ≤ J₁ ∧ IsPGroup 2 T₁ ∧ B ≤ Subgroup.normalizer (T₁ : Set G) ∧ ⁅B, T₁⁆ = T₁ ∧
      IsElemAbelian 2 (imageMod 3 J₁ T₁) ∧ Nat.card (imageMod 3 J₁ T₁) = 4 ∧
      GLAPPrimeCoreOf 3 J₁ ≤ GLAPPrimeCoreOf 3 L

end CFSG.LocalAnalysis.GLTheoremA
