module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndNat

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

section Defs

variable {V : Type} [CommGroup V]

@[expose] def diagImg (y : MulAut V) (W : Subgroup V) : Subgroup V := W.map y.toMonoidHom

@[expose] def DiagMinInv (K : Subgroup (MulAut V)) (W : Subgroup V) : Prop :=
  W ≠ ⊥ ∧ GInv K W ∧ ∀ A : Subgroup V, GInv K A → A ≤ W → A = ⊥ ∨ A = W

structure DiagPre (K K' Y : Subgroup (MulAut V)) (t : MulAut V) : Prop where
  t_sq : t * t = 1
  Kconj : K' = K.map (MulAut.conj t).toMonoidHom
  comm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a
  quasi : CFSG.Open.IsQuasisimple ↥K
  oddZ : Odd (Nat.card ↥(Subgroup.center ↥K))
  Y_mem : ∀ y : MulAut V, y ∈ Y ↔ ∃ k ∈ K, y = k * (t * k * t⁻¹)
  perfY : ⁅Y, Y⁆ = Y
  centerY : Subgroup.center ↥Y = ⊥
  simpleY : IsSimpleGroup ↥Y

structure DiagPair (K K' Y : Subgroup (MulAut V)) (t : MulAut V) : Prop extends
    DiagPre K K' Y t where
  irr : ∀ A : Subgroup V, GInv (K ⊔ K') A → A = ⊥ ∨ A = ⊤

variable [Finite V]

structure DiagCfg (G T Y K K' : Subgroup (MulAut V)) (t : MulAut V) : Prop extends
    DiagPre K K' Y t where
  Y_le : Y ≤ G
  T_le : T ≤ G
  T_cent : T ≤ Subgroup.centralizer (Y : Set (MulAut V))
  t_mem : t ∈ T
  cls : InClassX ↥(yuHol Y) ∨
    ∃ n : ℕ, 2 ≤ n ∧ IsNatSectionBy (omegaMinusAct n) Y (commV Y) ⊥
  L_eq : conjClosure Y G = K ⊔ K'
  gen : K ⊔ K' ⊔ T = G
  irr : ∀ A : Subgroup V, GInv G A → A = ⊥ ∨ A = ⊤

structure DiagCoreOut (K K' : Subgroup (MulAut V)) (n : ℕ) : Prop where
  iso : Nonempty (↥K ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq n))
  disj : K ⊓ K' = ⊥
  split : ∀ W : Subgroup V, DiagMinInv K W →
    ∃ θ : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq n), IsNatSectionWith (slAct n) θ W ⊥ ∧
      ∃ k₀ ∈ K', W ⊓ diagImg k₀ W = ⊥ ∧ W ⊔ diagImg k₀ W = ⊤

end Defs

@[expose] def DiagMod_irr : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (G T Y K K' : Subgroup (MulAut V)) (t : MulAut V), DiagCfg G T Y K K' t →
      ∀ A : Subgroup V, GInv (K ⊔ K') A → A = ⊥ ∨ A = ⊤

@[expose] def DiagMod_sel : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (K K' Y : Subgroup (MulAut V)) (t : MulAut V), DiagPair K K' Y t →
      ∀ W : Subgroup V, DiagMinInv K W →
        (∀ S : Set (MulAut V), S ⊆ (Y : Set (MulAut V)) → Subgroup.closure S = Y →
          ∃ y ∈ S, ∃ w ∈ W, y w ∉ W) ∧
        (∀ y ∈ Y, (∃ w ∈ W, y w ∉ W) →
          W ⊓ diagImg y W = ⊥ ∧ Nat.card ↥W ≤ Nat.card ↥(commV (Subgroup.zpowers y)))

@[expose] def DiagMod_s2 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (K K' Y : Subgroup (MulAut V)) (t : MulAut V), DiagPair K K' Y t →
      ∀ f : ℕ, 2 ≤ f → Nonempty (↥Y ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq f)) →
        Nonempty (↥K ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq f)) ∧ K ⊓ K' = ⊥

@[expose] def DiagBoundSL : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (Y : Subgroup (MulAut V)) (n : ℕ), 2 ≤ n →
      IsNatSectionBy (slAct n) Y (commV Y) (commV Y ⊓ fixV Y) →
        ∀ y ∈ Y, Odd (orderOf y) → Nat.card ↥(commV (Subgroup.zpowers y)) ≤ 2 ^ (2 * n)

@[expose] def DiagBoundAlt : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (Y : Subgroup (MulAut V)) (m : ℕ), 5 ≤ m → Odd m →
      IsNatSectionBy (altAct m) Y (commV Y) (commV Y ⊓ fixV Y) →
        ∃ y ∈ Y, orderOf y = 3 ∧ Nat.card ↥(commV (Subgroup.zpowers y)) ≤ 4

@[expose] def DiagBoundMinus : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (Y : Subgroup (MulAut V)) (n : ℕ), 2 ≤ n →
      IsNatSectionBy (omegaMinusAct n) Y (commV Y) ⊥ →
        ∃ y ∈ Y, y ≠ 1 ∧ Odd (orderOf y) ∧
          Nat.card ↥(commV (Subgroup.zpowers y)) < 2 ^ (4 * n)

@[expose] def DiagMod_ident : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (K K' : Subgroup (MulAut V)) (n : ℕ), 2 ≤ n →
      (∀ a ∈ K, ∀ b ∈ K', a * b = b * a) →
      Nonempty (↥K ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq n)) → Nat.card ↥K' = Nat.card ↥K →
        ∀ W : Subgroup V, DiagMinInv K W → (∃ k ∈ K, ∃ w ∈ W, k w ≠ w) →
          Nat.card ↥W = 2 ^ (2 * n) →
          ∀ k₀ ∈ K', W ⊓ diagImg k₀ W = ⊥ → W ⊔ diagImg k₀ W = ⊤ →
            ∃ θ : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq n), IsNatSectionWith (slAct n) θ W ⊥

@[expose] def DiagMod_core : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (K K' Y : Subgroup (MulAut V)) (t : MulAut V), DiagPair K K' Y t →
      ∀ n : ℕ, 2 ≤ n → IsNatSectionBy (slAct n) Y (commV Y) (commV Y ⊓ fixV Y) →
        DiagCoreOut K K' n

@[expose] def DiagMod_alt : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (K K' Y : Subgroup (MulAut V)) (t : MulAut V), DiagPair K K' Y t →
      ((∃ m : ℕ, 5 ≤ m ∧ Odd m ∧
          IsNatSectionBy (altAct m) Y (commV Y) (commV Y ⊓ fixV Y)) ∨
        (InClassX ↥(yuHol Y) ∧ ∃ m : ℕ, 7 ≤ m ∧ Odd m ∧
          Nonempty (↥Y ≃* alternatingGroup (Fin m)))) → False

@[expose] def DiagMod_minus : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (K K' Y : Subgroup (MulAut V)) (t : MulAut V), DiagPair K K' Y t →
      ∀ n : ℕ, 2 ≤ n → IsNatSectionBy (omegaMinusAct n) Y (commV Y) ⊥ → False

@[expose] def DiagMod_nat : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (K K' : Subgroup (MulAut V)) (n : ℕ), 2 ≤ n →
      (∀ a ∈ K, ∀ b ∈ K', a * b = b * a) → ⁅K', K'⁆ = K' → Nat.card ↥K' = Nat.card ↥K →
        ∀ (θ : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq n)) (W : Subgroup V),
          IsNatSectionWith (slAct n) θ W ⊥ →
          ∀ k₀ ∈ K', W ⊓ diagImg k₀ W = ⊥ → W ⊔ diagImg k₀ W = ⊤ →
            IsNatSectionBy (omegaPlusAct n) (K ⊔ K') (commV (K ⊔ K')) ⊥

@[expose] def DiagMod_count : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (K K' Y : Subgroup (MulAut V)) (t : MulAut V), DiagPair K K' Y t →
      ∀ n : ℕ, 2 ≤ n → IsNatSectionBy (slAct n) Y (commV Y) (commV Y ⊓ fixV Y) →
        DiagCoreOut K K' n → Nat.card ↥(commV Y) = 2 ^ (3 * n)

end CFSG.CGT.PushingUpLit.CGT6
