module

public import CFSG.GH74.Uniqueness.SU.KInputs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH74.Uniqueness.SU.K

open Subgroup CFSG.Blueprint

@[expose] def OneInvClass (H : Type*) [Group H] : Prop :=
  ∀ u v : H, orderOf u = 2 → orderOf v = 2 → IsConj u v

abbrev CBar (H : Type*) [Group H] (z : H) : Type _ :=
  ↥(centralizer ({z} : Set H)) ⧸ pPrimeCore 2 ↥(centralizer ({z} : Set H))

@[expose] def OC (H : Type*) [Group H] (z : H) : Subgroup H :=
  (pPrimeCore 2 ↥(centralizer ({z} : Set H))).map (centralizer ({z} : Set H)).subtype

@[expose] def KI7a : Prop :=
  ∀ n : ℕ, (n = 8 ∨ n = 9 ∨ n = 10) → ∀ (X : Type) [Group X] [Finite X], IsTwoAlt X n →
    ∀ u v : X, orderOf u = 2 → orderOf v = 2 → u ∉ center X → v ∉ center X → IsConj u v

@[expose] def KI7b : Prop :=
  ∀ n : ℕ, 5 ≤ n → ∀ (X : Type) [Group X] [Finite X], IsTwoAlt X n →
    Open.twoRank X = 3 * (n / 8) + 1

@[expose] def KI7c : Prop :=
  ∀ n : ℕ, (n = 8 ∨ n = 9) → ∀ (X : Type) [Group X] [Finite X], IsTwoAlt X n →
    ∀ A Y : Subgroup X, Open.IsElemAbelian 2 A → Open.pRank 2 A = Open.twoRank X →
      A ≤ normalizer (Y : Set X) → Odd (Nat.card Y) → Y = ⊥

@[expose] def KI7d : Prop :=
  ∀ n : ℕ, (n = 9 ∨ n = 10) → ∀ (X : Type) [Group X] [Finite X], IsTwoAlt X n →
    ∀ a : X, orderOf a = 2 → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ Y : Subgroup X, IsPGroup p Y →
      (∀ y ∈ Y, a * y * a⁻¹ = y⁻¹) →
        Nat.card Y ∣ 5 ^ (if n = 9 then 1 else 2) ∨ Nat.card Y ∣ 7 ∨ Nat.card Y ∣ 9

@[expose] def KI7 : Prop := KI7a ∧ KI7b ∧ KI7c ∧ KI7d

@[expose] def KI8 : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SU0.GHGroup H → pPrimeCore 2 H = ⊥ → OneInvClass H →
    ∀ (T : Sylow 2 H) (z : H), z ∈ (T : Subgroup H) → orderOf z = 2 →
      (∀ t ∈ (T : Subgroup H), t * z = z * t) →
      (Nonempty (CBar H z ≃* GL (Fin 2) (ZMod 3)) →
        (NativeSporadic.IsSporadic H .M11 ∨ LieModel H .PSL 3 3 1) ∧
          pPrimeCore 2 ↥(centralizer ({z} : Set H)) = ⊥) ∧
      (Nonempty (CBar H z ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
        Open.IsElemAbelian 3 (OC H z) →
          (OC H z = ⊥ ∧ (Nonempty (H ≃* alternatingGroup (Fin 4)) ∨ LieModel H .PSL 2 5 1)) ∨
          (Nat.card (OC H z) = 3 ∧ (LieModel H .PSL 2 11 1 ∨ LieModel H .PSL 2 13 1))) ∧
      (IsTwoAlt (CBar H z) 8 →
        NativeSporadic.IsSporadic H .McL ∧ pPrimeCore 2 ↥(centralizer ({z} : Set H)) = ⊥)

end CFSG.GH74.Uniqueness.SU.K
