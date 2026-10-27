module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFMod

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.Quasithin Subgroup

@[expose] def NatN (n : ℕ) {S : Type} [CommGroup S] (L : Subgroup (MulAut S)) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
    ∃ (ε : ↥L ≃* ↥(StatedSU 4 (2 ^ n) F)) (ψ : S ≃* Multiplicative (Fin 4 → F)),
      ∀ (l : ↥L) (s : S), ψ ((l : MulAut S) s) = Multiplicative.ofAdd
        (((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).mulVec
          (Multiplicative.toAdd (ψ s)))

@[expose] def NatO (n : ℕ) {S : Type} [CommGroup S] (L : Subgroup (MulAut S)) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (b c : F), Nat.card F = 2 ^ n ∧
    (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
    ∃ (ε : ↥L ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)))
      (ψ : S ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)),
      ∀ (l : ↥L) (s : S), ψ ((l : MulAut S) s) = Multiplicative.ofAdd
        (((ε l : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).mulVec
          (Multiplicative.toAdd (ψ s)))

theorem naturalU4Mod_iff {n : ℕ} {S : Type} [CommGroup S] {L : Subgroup (MulAut S)} :
    NaturalU4Mod n L ↔ NatN n L ∨ NatO n L := Iff.rfl

@[expose] def PartBNStmt : Prop :=
  ∀ {S : Type} [CommGroup S] [Finite S], (∀ s : S, s ^ 2 = 1) → ∀ {n : ℕ}, 1 ≤ n →
    ∀ {F : Type} [Field F] [Finite F], Nat.card F = (2 ^ n) ^ 2 →
    ∀ {L A : Subgroup (MulAut S)} (ε : ↥L ≃* ↥(StatedSU 4 (2 ^ n) F))
      (ψ : S ≃* Multiplicative (Fin 4 → F)),
      (∀ (l : ↥L) (s : S), ψ ((l : MulAut S) s) = Multiplicative.ofAdd
        (((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).mulVec
          (Multiplicative.toAdd (ψ s)))) →
      IsElemAbelian2 A → A ≤ Subgroup.normalizer (L : Set (MulAut S)) →
      Nat.card A * Nat.card (fixV A) ≤ Nat.card S

@[expose] def PartBOStmt : Prop :=
  ∀ {S : Type} [CommGroup S] [Finite S], (∀ s : S, s ^ 2 = 1) → ∀ {n : ℕ}, 1 ≤ n →
    ∀ {F : Type} [Field F] [Finite F] {b c : F}, Nat.card F = 2 ^ n →
    (∀ s : F, s ^ 2 + b * s + c ≠ 0) →
    ∀ {L A : Subgroup (MulAut S)} (ε : ↥L ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)))
      (ψ : S ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)),
      (∀ (l : ↥L) (s : S), ψ ((l : MulAut S) s) = Multiplicative.ofAdd
        (((ε l : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).mulVec
          (Multiplicative.toAdd (ψ s)))) →
      IsElemAbelian2 A → A ≤ Subgroup.normalizer (L : Set (MulAut S)) →
      Nat.card A * Nat.card (fixV A) ≤ 2 * Nat.card S

@[expose] def PartBO4Stmt : Prop :=
  ∀ {S : Type} [CommGroup S] [Finite S], (∀ s : S, s ^ 2 = 1) → ∀ {n : ℕ}, 1 ≤ n →
    ∀ {F : Type} [Field F] [Finite F] {b c : F}, Nat.card F = 2 ^ n →
    (∀ s : F, s ^ 2 + b * s + c ≠ 0) →
    ∀ {L A : Subgroup (MulAut S)} (ε : ↥L ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)))
      (ψ : S ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)),
      (∀ (l : ↥L) (s : S), ψ ((l : MulAut S) s) = Multiplicative.ofAdd
        (((ε l : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).mulVec
          (Multiplicative.toAdd (ψ s)))) →
      IsElemAbelian2 A → A ≤ Subgroup.normalizer (L : Set (MulAut S)) →
      ¬ (Nat.card A = 4 ∧ Nat.card S = 2 * Nat.card (fixV A))

structure TorusSetting {V : Type} [CommGroup V] (L D : Subgroup (MulAut V)) (M₀ M₁ : Subgroup V) :
    Prop where
  simple : IsSimpleGroup ↥L
  nonab : ∃ a b : ↥L, a * b ≠ b * a
  Dcomm : ∀ d ∈ D, ∀ e ∈ D, d * e = e * d
  Dsq : ∀ d ∈ D, d * d = 1
  DL : ∀ d ∈ D, ∀ l ∈ L, d * l = l * d
  le : M₀ ≤ M₁
  le_Y : M₁ ≤ commV L ⊓ fixV D
  inv : L ≤ stabSub M₁
  triv₀ : LTrivOn L ⊥ M₀
  triv_top : LTrivOn L M₁ (commV L ⊓ fixV D)
  nc : ¬ LTrivOn L M₀ M₁

theorem TorusSetting.stab₀ {V : Type} [CommGroup V] {L D : Subgroup (MulAut V)}
    {M₀ M₁ : Subgroup V} (h : TorusSetting L D M₀ M₁) : L ≤ stabSub M₀ := by
  have key : ∀ g ∈ L, ∀ z ∈ M₀, g z ∈ M₀ := by
    intro g hg z hz
    have := h.triv₀ g hg z hz
    rw [Subgroup.mem_bot, mul_inv_eq_one] at this
    rw [this]
    exact hz
  exact fun g hg => mem_stabSub_of_inv (key g hg) (key g⁻¹ (L.inv_mem hg))

@[expose] def TorusStepN : Prop :=
  ∀ {V : Type} [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ {n : ℕ} {L D : Subgroup (MulAut V)} {M₀ M₁ : Subgroup V}, TorusSetting L D M₀ M₁ →
      NatN n (autSec L M₁ M₀) →
      Nat.card (commV L) ≤ Nat.card (autSub D (commV L)) * Nat.card ↥(commV L ⊓ fixV D) →
      commV L ≤ fixV D

@[expose] def TorusStepO : Prop :=
  ∀ {V : Type} [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ {n : ℕ} {L D : Subgroup (MulAut V)} {M₀ M₁ : Subgroup V}, TorusSetting L D M₀ M₁ →
      NatO n (autSec L M₁ M₀) →
      Nat.card (commV L) ≤ 2 * Nat.card (autSub D (commV L)) * Nat.card ↥(commV L ⊓ fixV D) →
      commV L ≤ fixV D

end CFSG.LocalAnalysis.RankThreeUC
