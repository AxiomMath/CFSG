module

public import CFSG.LocalAnalysis.GLTheoremA.S6.AltDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def isSporIdx (s : TauCeti.SporadicName) : TauCeti.CFSGIndex → Prop
  | .sporadic s' => s' = s
  | _ => False

@[expose] def IsSporType {G : Type} [Group G] (p : ℕ) (K : Subgroup G) (s : TauCeti.SporadicName) : Prop :=
  catalogIs (PSimple p K) (isSporIdx s)

@[expose] def I203At : Prop :=
  ∀ (p n : ℕ), p.Prime → p ≠ 2 → p ∣ n → 5 ≤ n → ∀ (Q : Type) [Group Q]
    (_ : Q ≃* ↥(alternatingGroup (Fin n))) (E U : Subgroup Q),
    IsElemAbelian p E → Nat.card ↥E = p ^ (n / p) → IsPGroup 2 U →
    E ≤ Subgroup.normalizer (U : Set Q) → U = ⊥

@[expose] def I1415NineAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K J : Subgroup G) (y : G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X K →
    y ∈ Subgroup.normalizer (K : Set G) → y ^ 3 = 1 →
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set G)) J → IsAltPType 3 J 9 →
    (∃ k : ℕ, IsAltPType 3 K (9 + 3 * k)) ∨ IsSporType 3 K .HN ∨ IsSporType 3 K .Co1

@[expose] def I1415SevenAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K J : Subgroup G) (y : G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X K →
    y ∈ Subgroup.normalizer (K : Set G) → y ^ 3 = 1 →
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set G)) J → IsAltPType 3 J 7 →
    (∃ k : ℕ, IsAltPType 3 K (7 + 3 * k)) ∨ IsSporType 3 K .He

@[expose] def I1422At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K J : Subgroup G) (y : G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X K →
    y ∈ Subgroup.normalizer (K : Set G) → y ^ 3 = 1 →
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set G)) J → IsAltPType 3 J 8 →
    Nonempty (↥(imageMod 3 K J) ≃* ↥(alternatingGroup (Fin 8)))

@[expose] def I2014At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K J I R : Subgroup G) (y : G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X K →
    IsSporType 3 K .HN → y ∈ Subgroup.normalizer (K : Set G) → y ^ 3 = 1 →
    ¬ CentMod 3 K y → GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set G)) J →
    IsAltPType 3 J 9 → I ≤ J → IsAltPType 3 I 8 → R ≤ K → IsPGroup 2 R →
    I ≤ Subgroup.normalizer (R : Set G) → y ∈ Subgroup.normalizer (R : Set G) →
    imageMod 3 K I ≤ Subgroup.centralizer ((imageMod 3 K R : Subgroup (PQuot 3 K)) : Set (PQuot 3 K))

@[expose] def I1016CoAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K : Subgroup G), GLAPComponent 3 X K → IsSporType 3 K .Co1 →
    Subgroup.center (PQuot 3 K) = ⊥ ∧
    ∃ E U : Subgroup G, E ≤ K ∧ IsElemAbelian 3 E ∧ Nat.card ↥E = 3 ^ 4 ∧ U ≤ K ∧ IsPGroup 2 U ∧
      ¬ U ≤ GLAPPrimeCoreOf 3 K ∧ E ≤ Subgroup.normalizer (U : Set G)

@[expose] def KLevelAltAt : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q → GLAPPrimeCore 3 Q = ⊥ →
    ((catalogIs (Q ⧸ Subgroup.center Q) (isAltN 7) ∨ catalogIs (Q ⧸ Subgroup.center Q) (isAltN 10)) →
      fullCoverLevel 3 Q = 3) ∧
    (((∃ m : ℕ, 11 ≤ m ∧ catalogIs (Q ⧸ Subgroup.center Q) (isAltN m)) ∨
      catalogIs (Q ⧸ Subgroup.center Q) (isSporIdx .He)) → fullCoverLevel 3 Q = 4)

@[expose] def I182At (G : Type) [Group G] [Finite G] : Prop :=
  CFSG.Open.IsKProper G → ∀ D E : Subgroup G, IsPGroup 3 D → IsPGroup 3 E →
    (∀ d ∈ D, ∀ e ∈ E, d * e = e * d) →
    GLAPLayer 3 (GLAPLayer 3 (Subgroup.centralizer (D : Set G)) ⊓ Subgroup.centralizer (E : Set G)) =
      GLAPLayer 3 (Subgroup.centralizer (D : Set G) ⊓ Subgroup.centralizer (E : Set G))

@[expose] def I2ProdAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (a x : G) (M K J : Subgroup G), GLAPComponent 3 (Subgroup.centralizer ({a} : Set G)) M →
    GLBConj x M ≠ M → GLBConj x (GLBConj x M) ≠ M →
    K = M ⊔ GLBConj x M ⊔ GLBConj x (GLBConj x M) → x ∈ Subgroup.centralizer ({a} : Set G) →
    x ^ 3 = 1 → ∀ hJK : J ≤ K, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x} : Set G)) J →
    ∃ φ : PSimple 3 K ≃* (PSimple 3 M × PSimple 3 M × PSimple 3 M),
      ∃ ψ₁ ψ₂ ψ₃ : PSimple 3 J ≃* PSimple 3 M, ∀ j : ↥J,
        φ (QuotientGroup.mk (QuotientGroup.mk (⟨(j : G), hJK j.2⟩ : ↥K))) =
          (ψ₁ (QuotientGroup.mk (QuotientGroup.mk j)), ψ₂ (QuotientGroup.mk (QuotientGroup.mk j)),
            ψ₃ (QuotientGroup.mk (QuotientGroup.mk j)))

@[expose] def I2017At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K D J I R : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X K →
    D ≤ Subgroup.normalizer (K : Set G) → IsElemAbelian 3 D → Nat.card ↥D = 9 →
    (∃ d ∈ D, d ≠ 1 ∧ CentMod 3 K d) →
    (∀ E : Subgroup G, E ≤ (K ⊔ D) ⊓ Subgroup.centralizer (D : Set G) → IsElemAbelian 3 E →
      Nat.card ↥E ≤ 3 ^ 4) →
    GLAPLayer 3 (K ⊓ Subgroup.centralizer (D : Set G)) = J →
    GLAPComponent 3 (K ⊓ Subgroup.centralizer (D : Set G)) J →
    Nonempty (↥(imageMod 3 K J) ≃* ↥(alternatingGroup (Fin 8))) → I ≤ J →
    Nonempty (↥(imageMod 3 K I) ≃* ↥(alternatingGroup (Fin 7))) → R ≤ K → IsPGroup 2 R →
    I ⊔ D ≤ Subgroup.normalizer (R : Set G) →
    ¬ imageMod 3 K I ≤ Subgroup.centralizer ((imageMod 3 K R : Subgroup (PQuot 3 K)) : Set (PQuot 3 K)) →
    IsL62Type 3 K

@[expose] def I264ChevTwoAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (B : Subgroup G) (x : G) (K : Subgroup G), IsElemAbelian p B → x ∈ B →
    x ≠ 1 → GLAPComponent p (Subgroup.centralizer ({x} : Set G)) K → CFSG.Open.IsKGroup ↥K →
    B ≤ Subgroup.normalizer (K : Set G) → p ^ 4 ≤ Nat.card ↥B → IsMaxRankIn p B (K ⊔ B) →
    IsChevSimple 2 (PSimple p K) →
    (∃ U : Subgroup G, U ≤ K ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set G) ∧
      ¬ U ≤ GLAPPrimeCoreOf p K) → IsGB p B K

@[expose] def I61L62At : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], commutator Q = ⊤ →
    catalogIs (Q ⧸ Subgroup.center Q) (onLie fun d => d = .A 5 gfTwoPP) → Nat.card (Subgroup.center Q) = 1

@[expose] def I106L62At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ K : Subgroup G, IsL62Type 3 K → (∀ E : Subgroup G, E ≤ K → IsElemAbelian 3 E → Nat.card ↥E ≤ 3 ^ 3) ∧
    ∃ E U : Subgroup G, E ≤ K ∧ IsElemAbelian 3 E ∧ Nat.card ↥E = 3 ^ 3 ∧ U ≤ K ∧ IsPGroup 2 U ∧
      ¬ U ≤ GLAPPrimeCoreOf 3 K ∧ E ≤ Subgroup.normalizer (U : Set G)

@[expose] def I71L62At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ K : Subgroup G, IsL62Type 3 K → ∀ b ∈ Subgroup.normalizer (K : Set G),
    IsPGroup 3 (Subgroup.zpowers b) → InducesInnerMod 3 K b

@[expose] def I131L62At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K Do J I S : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X K → IsL62Type 3 K →
    S ≤ K → IsPGroup 2 S → ¬ S ≤ GLAPPrimeCoreOf 3 K → Do ≤ K → Nat.card ↥Do = 3 →
    I ≤ K → (∀ d ∈ Do, ∀ i ∈ I, d * i = i * d) → Nonempty (↥(imageMod 3 K I) ≃* ↥(alternatingGroup (Fin 7))) →
    Do ⊔ I ≤ Subgroup.normalizer (S : Set G) → J ≤ K → I ≤ J →
    GLAPLayer 3 (K ⊓ Subgroup.centralizer (Do : Set G)) = J →
    Nonempty (↥(imageMod 3 K J) ≃* ↥(alternatingGroup (Fin 8))) →
    imageMod 3 K J ≤ Subgroup.normalizer ((imageMod 3 K S : Subgroup (PQuot 3 K)) : Set (PQuot 3 K))

end CFSG.LocalAnalysis.GLTheoremA
