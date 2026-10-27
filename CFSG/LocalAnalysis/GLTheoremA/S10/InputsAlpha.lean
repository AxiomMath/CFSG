module

public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

namespace S10

variable {G : Type} [Group G] [Finite G]

@[expose] def isG2n (n : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun | .G2 q => q.p = 2 ∧ q.exponent = n | _ => False

@[expose] def isUrn (n : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA r q => 2 ≤ r ∧ q.p = 2 ∧ q.exponent = n | _ => False

@[expose] def isU33 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA 2 q => q.card = 3 | _ => False

@[expose] def InYK (y : G) (K B : Subgroup G) : Prop :=
  ∀ g ∈ B, ∃ (i : ℤ) (k : G), k ∈ K ∧ g = y ^ i * k

@[expose] def IsBmaxIn (p : ℕ) (X B : Subgroup G) : Prop :=
  B ≤ X ∧ IsElemAbelian p B ∧ Nat.card B = p ^ GLATwoLocalRank p ↥X ∧
    ∃ U : Subgroup G, U ≤ X ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set G)

@[expose] def IsE0 (B K E : Subgroup G) : Prop :=
  E ≤ B ∧ GLAPLayer 3 (K ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥ ∧
    ∀ E' : Subgroup G, E' ≤ B → GLAPLayer 3 (K ⊓ Subgroup.centralizer (E' : Set G)) ≠ ⊥ →
      Nat.card E' ≤ Nat.card E

end S10

@[expose] def I1428At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (X K B : Subgroup G), CFSG.Open.IsKGroup ↥X → S10.IsBmaxIn p X B →
    GLAPComponent p X K → IsChevSimple 2 (PSimple p K) →
    GLAMarking (PQuot p K) (fun lab _ _ _ _ _ => p ∣ lab.n) →
    B ≤ Subgroup.normalizer (K : Set G) ∧ ∀ y ∈ B, y ≠ 1 →
      ((∀ M : Subgroup G, GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set G)) M →
          B ≤ Subgroup.normalizer (M : Set G)) ∨
        (p = 3 ∧ ∃ m : ℕ, Odd m ∧ 1 < m ∧ catalogIs (PSimple 3 K) (S10.isU6n m) ∧
          ∀ M : Subgroup G, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set G)) M →
            catalogIs (PSimple 3 M) (S10.isL2n m)))

@[expose] def I112NormAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K B : Subgroup G) (n : ℕ), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X K → IsElemAbelian 3 B → B ≤ X →
    3 ^ GLATwoLocalRank 3 ↥X ≤ Nat.card B → Odd n → 1 < n →
    (catalogIs (PSimple 3 K) (S10.isU6n n) ∨ catalogIs (PSimple 3 K) (S10.isTE6n n)) →
    B ≤ Subgroup.normalizer (K : Set G)

@[expose] def I1015twoAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K : Subgroup G) (n : ℕ), GLAPComponent 3 X K → Odd n →
    (catalogIs (PSimple 3 K) (S10.isU6n n) →
      ∃ E T : Subgroup G, E ≤ K ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧ T ≤ K ∧ IsPGroup 2 T ∧
        ¬ T ≤ GLAPPrimeCoreOf 3 K ∧ E ≤ Subgroup.normalizer (T : Set G)) ∧
    (catalogIs (PSimple 3 K) (S10.isTE6n n) →
      ∃ E T : Subgroup G, E ≤ K ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧ T ≤ K ∧ IsPGroup 2 T ∧
        ¬ T ≤ GLAPPrimeCoreOf 3 K ∧ E ≤ Subgroup.normalizer (T : Set G))

@[expose] def I263AlphaAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (y : G) (K B' : Subgroup G) (n : ℕ), GLAIsBmax 3 B' → y ∈ B' → GLAPComponent 3 (Subgroup.centralizer ({y} : Set G)) K →
    S10.InYK y K B' → Odd n → 1 < n →
    (catalogIs (PSimple 3 K) (S10.isU6n n) ∨ catalogIs (PSimple 3 K) (S10.isTE6n n)) →
    (∃ T : Subgroup G, T ≤ K ∧ IsPGroup 2 T ∧ B' ≤ Subgroup.normalizer (T : Set G) ∧
      ¬ T ≤ GLAPPrimeCoreOf 3 K) → IsGB 3 B' K

@[expose] def I266At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K B : Subgroup G) (n : ℕ), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X K →
    (catalogIs (PSimple 3 K) (S10.isG2n n) ∨ (Odd n ∧ 1 < n ∧ catalogIs (PSimple 3 K) (S10.isU6n n))) →
    (catalogIs (PSimple 3 K) (S10.isG2n n) → Subgroup.center (PQuot 3 K) = ⊥) →
    (catalogIs (PSimple 3 K) (S10.isG2n n) → GLAPPrimeCoreOf 3 K = ⊥) →
    (catalogIs (PSimple 3 K) (S10.isU6n n) → GLAPPrimeCoreOf 3 K = ⊥) →
    (catalogIs (PSimple 3 K) (S10.isU6n n) → ∃ k : ℕ, Nat.card (Subgroup.center (PQuot 3 K)) = 3 ^ k) →
    IsElemAbelian 3 B → B ≤ Subgroup.normalizer (K : Set G) → B ≤ X → 3 ^ GLATwoLocalRank 3 ↥X ≤ Nat.card B →
    3 ^ 2 * Nat.card ↥(B ⊓ centModSubgroup 3 K) ≤ Nat.card B → InnDiagOn 3 B K →
    (∃ T : Subgroup G, T ≤ K ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      ¬ T ≤ GLAPPrimeCoreOf 3 K ∧ (⁅T, B⁆ : Subgroup G) ≠ ⊥) →
    (∀ E : Subgroup G, S10.IsE0 B K E → ¬ ∀ g ∈ E, CentMod 3 K g) →
    ∃ (E : Subgroup G) (y : G) (J : Subgroup G), S10.IsE0 B K E ∧ y ∈ E ∧ ¬ CentMod 3 K y ∧
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set G)) J ∧
      ((catalogIs (PSimple 3 K) (S10.isG2n n) → Even n ∧ catalogIs (PSimple 3 J) (S10.isL2n n)) ∧
        (catalogIs (PSimple 3 K) (S10.isU6n n) → catalogIs (PSimple 3 J) (S10.isUrn n))) ∧
      ∃ T : Subgroup G, T ≤ K ⊓ Subgroup.centralizer ({y} : Set G) ∧ IsPGroup 2 T ∧
        B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, B⁆ : Subgroup G) ≠ ⊥ ∧ IsEmpty (T ≃* QuaternionGroup 2)

@[expose] def OutCyclicAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (x : G) (L A : Subgroup G), IsSTriple p B x L →
    CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) → IsChevSimple 2 (PSimple p L) →
    B ≤ Subgroup.normalizer (L : Set G) → A ≤ B →
    ∃ A₀ : Subgroup G, A₀ ≤ A ∧ InnDiagOn p A₀ L ∧ Nat.card A ≤ p * Nat.card A₀ ∧
      ∀ a ∈ A, InnDiagOn p (Subgroup.zpowers a) L → a ∈ A₀

@[expose] def InnDiagIsoAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (X X' J K : Subgroup G) (y : G) (e : PSimple p J ≃* PSimple p K), GLAPComponent p X J →
    GLAPComponent p X' K → IsChevSimple 2 (PSimple p K) → y ∈ Subgroup.normalizer (J : Set G) →
    y ∈ Subgroup.normalizer (K : Set G) → IsoPresAct p y J K e →
    InnDiagOn p (Subgroup.zpowers y) J → InnDiagOn p (Subgroup.zpowers y) K

@[expose] def I148fiveAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K I' J : Subgroup G) (x y : G) (n : ℕ), GLAPComponent 3 X K → IsChevSimple 2 (PSimple 3 K) → IsTD4 3 K → x ^ 3 = 1 → y ^ 3 = 1 →
    x * y = y * x → y ∉ Subgroup.zpowers x → NonInner 3 x K → GLAPComponent 3 (K ⊓ cx x) I' → IsG2Quot 3 I' →
    InnDiagOn 3 (Subgroup.zpowers y) K → GLAPComponent 3 (I' ⊓ cx y) J → catalogIs (PSimple 3 J) (S10.isL2n n) →
    ∃ M₀ : Subgroup G, GLAPComponent 3 (K ⊓ cx y) M₀ ∧ (∀ M : Subgroup G, GLAPComponent 3 (K ⊓ cx y) M → M = M₀) ∧
      catalogIs (PSimple 3 M₀) (S10.isL2n (3 * n)) ∧ FieldOn 3 x M₀

@[expose] def L2CentAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (Y W : Subgroup G) (𝒞 : Set (Subgroup G)) (x : G) (m : ℕ),
    (∀ M ∈ 𝒞, GLAPComponent 3 Y M ∧ catalogIs (PSimple 3 M) (S10.isL2n m)) → W = ⨆ M ∈ 𝒞, M →
    x ∈ Subgroup.normalizer (W : Set G) → x ^ 3 = 1 →
    ∀ K : Subgroup G, GLAPComponent 3 (W ⊓ cx x) K → ∃ k : ℕ, catalogIs (PSimple 3 K) (S10.isL2n k)

@[expose] def I112OneAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (X L B : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent p X L →
    IsElemAbelian p B → B ≤ X → p ^ GLATwoLocalRank p ↥X ≤ Nat.card B →
    ¬ B ≤ Subgroup.normalizer (L : Set G) →
    p = 3 ∧ Nat.card B = 3 * Nat.card ↥(B ⊓ Subgroup.normalizer (L : Set G))

structure MultAlphaAt (G : Type) [Group G] [Finite G] : Prop where
  g2 : ∀ (X L : Subgroup G) (b : G) (n : ℕ), GLAPComponent 3 X L → CFSG.Open.IsQuasisimple ↥L → b ^ 3 = 1 →
    R2Prop 3 b L → GLAPComponent 3 (L ⊓ cx b) (Ipart 3 L b) →
    catalogIs (PSimple 3 (Ipart 3 L b)) (S10.isG2n n) →
    GLAPPrimeCoreOf 3 (Ipart 3 L b) = ⊥ ∧ Subgroup.center (PQuot 3 (Ipart 3 L b)) = ⊥
  u6 : ∀ (X K : Subgroup G) (n : ℕ), GLAPComponent 3 X K → Odd n → 1 < n →
    catalogIs (PSimple 3 K) (S10.isU6n n) → ∃ k : ℕ, Nat.card (Subgroup.center (PQuot 3 K)) = 3 ^ k
  u6core : ∀ (X L : Subgroup G) (b : G) (n : ℕ), GLAPComponent 3 X L → CFSG.Open.IsQuasisimple ↥L → b ^ 3 = 1 →
    IsChevSimple 2 (PSimple 3 L) →
    R2Prop 3 b L → GLAPComponent 3 (L ⊓ cx b) (Ipart 3 L b) → Odd n → 1 < n →
    catalogIs (PSimple 3 (Ipart 3 L b)) (S10.isU6n n) → GLAPPrimeCoreOf 3 (Ipart 3 L b) = ⊥

@[expose] def I91U6At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L : Subgroup G) (b : G) (I' : Subgroup G) (n' : ℕ), GLAPComponent 3 X L → b ^ 3 = 1 → FieldOn 3 b L →
    GLAPComponent 3 (L ⊓ cx b) I' → Odd n' →
    (catalogIs (PSimple 3 L) (S10.isU6n (3 * n')) ↔ catalogIs (PSimple 3 I') (S10.isU6n n'))

@[expose] def I1015coverAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K : Subgroup G) (n : ℕ), GLAPComponent 3 X K → Odd n →
    (catalogIs (PSimple 3 K) (S10.isU6n n) ∨ catalogIs (PSimple 3 K) (S10.isTE6n n)) →
    Subgroup.center (PQuot 3 K) ≠ ⊥ →
    Nat.card (Subgroup.center (PQuot 3 K)) = 3 ∧
    (catalogIs (PSimple 3 K) (S10.isU6n n) →
      ∃ E T : Subgroup G, E ≤ K ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧ T ≤ K ∧ IsPGroup 2 T ∧
        ¬ T ≤ GLAPPrimeCoreOf 3 K ∧ E ≤ Subgroup.normalizer (T : Set G)) ∧
    (catalogIs (PSimple 3 K) (S10.isTE6n n) →
      ∃ E T : Subgroup G, E ≤ K ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 ∧ T ≤ K ∧ IsPGroup 2 T ∧
        ¬ T ≤ GLAPPrimeCoreOf 3 K ∧ E ≤ Subgroup.normalizer (T : Set G))

@[expose] def I1015fourU62At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K : Subgroup G), GLAPComponent 3 X K → catalogIs (PSimple 3 K) (S10.isU6n 1) →
    ∃ E T : Subgroup G, E ≤ K ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 3 * Nat.card (Subgroup.center (PQuot 3 K)) ∧ T ≤ K ∧ IsPGroup 2 T ∧
      ¬ T ≤ GLAPPrimeCoreOf 3 K ∧ E ≤ Subgroup.normalizer (T : Set G)

@[expose] def U62Type9At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K A T : Subgroup G), GLAPComponent 3 X K → catalogIs (PSimple 3 K) (S10.isU6n 1) →
    IsElemAbelian 3 A → 3 ^ 3 ≤ Nat.card A → A ≤ Subgroup.normalizer (K : Set G) →
    (∀ a ∈ A, a ≠ 1 → ¬ CentMod 3 K a) → InnDiagOn 3 A K →
    T ≤ K → IsPGroup 2 T → ¬ T ≤ GLAPPrimeCoreOf 3 K → A ≤ Subgroup.normalizer (T : Set G) →
    ∀ a ∈ A, a ≠ 1 → ∀ M : Subgroup G, GLAPComponent 3 (K ⊓ cx a) M →
      catalogIs (PSimple 3 M) (fun i => S9.isU4two i ∨ S9.isU5two i)

@[expose] def U33SolvCentAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X I : Subgroup G) (y : G), GLAPComponent 3 X I → catalogIs (PSimple 3 I) S10.isU33 →
    y ∈ Subgroup.normalizer (I : Set G) → y ^ 3 = 1 → ¬ CentMod 3 I y →
    GLAPLayer 3 (I ⊓ Subgroup.centralizer ({y} : Set G)) = ⊥

@[expose] def FieldU6ExpAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L : Subgroup G) (g : G) (m : ℕ), GLAPComponent 3 X L → FieldOn 3 g L →
    catalogIs (PSimple 3 L) (S10.isU6n m) → 3 ∣ m

@[expose] def G2CentrelessAt : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid),
    Subgroup.center (TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) = ⊥

end CFSG.LocalAnalysis.GLTheoremA
