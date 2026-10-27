module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdBalAct

public section

namespace CFSG.OddStandard.AltStdSmall4

open Subgroup Equiv AltStdCycTwo

section Perm

variable {n : ℕ}

theorem sign_swap_mul_swap {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    Perm.sign (swap a b * swap c d) = 1 := by
  rw [Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
  decide

abbrev pt (hn : 8 ≤ n) (i : ℕ) (hi : i < 8 := by omega) : Fin n := ⟨i, by omega⟩

@[expose] def quad (hn : 8 ≤ n) (a b c d e f g h : ℕ) (ha : a < 8 := by omega)
    (hb : b < 8 := by omega) (hc : c < 8 := by omega) (hd : d < 8 := by omega)
    (he : e < 8 := by omega) (hf : f < 8 := by omega) (hg : g < 8 := by omega)
    (hh : h < 8 := by omega) (hab : a ≠ b := by omega) (hcd : c ≠ d := by omega)
    (hef : e ≠ f := by omega) (hgh : g ≠ h := by omega) : alternatingGroup (Fin n) :=
  ⟨swap (pt hn a) (pt hn b) * swap (pt hn c) (pt hn d) *
      (swap (pt hn e) (pt hn f) * swap (pt hn g) (pt hn h)), by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul,
      sign_swap_mul_swap (by simp [Fin.ext_iff, hab]) (by simp [Fin.ext_iff, hcd]),
      sign_swap_mul_swap (by simp [Fin.ext_iff, hef]) (by simp [Fin.ext_iff, hgh]), mul_one]⟩

@[expose] def wBar (hn : 8 ≤ n) : alternatingGroup (Fin n) := quad hn 0 1 2 3 4 5 6 7

@[expose] def eBar (hn : 8 ≤ n) : Subgroup (alternatingGroup (Fin n)) :=
  closure {quad hn 0 1 2 3 4 5 6 7, quad hn 0 2 1 3 4 6 5 7, quad hn 0 4 1 5 2 6 3 7}

end Perm

section Objects

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ}

@[expose] def E (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) : Subgroup G :=
  ((eBar hn).map θ.symm.toMonoidHom).map L.subtype

@[expose] def w (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) : G :=
  (θ.symm (wBar hn) : G)

@[expose] def N0 (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (z : G) : Subgroup G :=
  normalizer ((E θ hn ⊔ zpowers z : Subgroup G) : Set G)

@[expose] def conjSub (z : G) (X : Subgroup G) : Subgroup G := X.map (MulAut.conj z).toMonoidHom

@[expose] def Hbar (T : Subgroup G) : Subgroup (MulAut T) := (AltStdBal.normAct T).range

end Objects

section Config

variable {G : Type} [Group G] [Finite G]

structure OrderTwoE (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G) : Prop where
  std : StandardSetting G L
  hn : 8 ≤ n
  cyc : AltStdBal.Cyc L Q z
  card : Nat.card Q = 2

theorem _root_.CFSG.OddStandard.AltStdCycTwo.OrderTwo.toE {L Q : Subgroup G} {n : ℕ}
    {θ : L ≃* alternatingGroup (Fin n)} {z : G} (h : OrderTwo G L Q n θ z) :
    OrderTwoE G L Q n θ z :=
  ⟨h.std, by have := h.hn; omega, h.cyc, h.card⟩

@[expose] def IsASmall {G : Type} [Group G] (L : Subgroup G) (n : ℕ) (z : G) : Prop :=
  (n = 8 ∨ n = 9) ∧ centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G)

structure Config (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G) : Prop where
  ot : OrderTwoE G L Q n θ z
  small : n ≤ 11
  shape : centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G) ∨
    (n ≤ 9 ∧ ∃ u ∈ centralizer ({z} : Set G), u ∉ L ⊔ centralizer (L : Set G) ∧ u ^ 2 = 1)

theorem Config.hn8 {L Q : Subgroup G} {n : ℕ} {θ : L ≃* alternatingGroup (Fin n)} {z : G}
    (c : Config G L Q n θ z) : 8 ≤ n :=
  c.ot.hn

theorem Config.n_cases {L Q : Subgroup G} {n : ℕ} {θ : L ≃* alternatingGroup (Fin n)} {z : G}
    (c : Config G L Q n θ z) : n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 := by
  have := c.ot.hn
  have := c.small
  omega

structure N0Data {L : Subgroup G} {n : ℕ} (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n)
    (z : G) (T : Subgroup G) : Prop where
  le : T ≤ N0 θ hn z
  homo : Nonempty (T ≃* Multiplicative (Fin 6 → ZMod 2)) ∨
    Nonempty (T ≃* Multiplicative (Fin 3 → ZMod 4))
  E_le : E θ hn ≤ T
  cent : T ⊓ centralizer ({z} : Set G) = E θ hn
  norm : z ∈ normalizer (T : Set G)
  normal : ∀ g ∈ N0 θ hn z, ∀ x ∈ T, g * x * g⁻¹ ∈ T ⊔ AltStdSec.oddCoreOf (N0 θ hn z)
  gen : N0 θ hn z ≤ (T ⊔ AltStdSec.oddCoreOf (N0 θ hn z)) ⊔ centralizer ({z} : Set G)

structure HData {L : Subgroup G} {n : ℕ} (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n)
    (z : G) (T : Subgroup G) : Prop where
  n0 : N0Data θ hn z T
  elem : ∀ x ∈ T, x ^ 2 = 1
  cent : centralizer (T : Set G) = T ⊔ AltStdSec.oddCoreOf (normalizer (T : Set G))
  inv : ∀ y ∈ T, (y * z) ^ 2 = 1 → ∃ x ∈ T, x * z * x⁻¹ = y * z

structure WreathStruct (z : G) (T : Subgroup G) : Prop where
  exists_factor : ∃ K₁ F₁ : Subgroup G, K₁ ≤ normalizer (T : Set G) ∧
    (∀ a ∈ K₁, ∀ b ∈ conjSub z K₁, a * b = b * a) ∧ K₁ ⊓ conjSub z K₁ = ⊥ ∧
    Nat.card (K₁ ⊓ T : Subgroup G) = 8 ∧ T = (K₁ ⊓ T) ⊔ conjSub z (K₁ ⊓ T) ∧
    F₁ ≤ K₁ ∧ F₁ ⊓ T = ⊥ ∧ (K₁ ⊓ T) ⊔ F₁ = K₁ ∧ Nat.card F₁ = 168 ∧
    centralizer ((K₁ ⊓ T : Subgroup G) : Set G) ⊓ K₁ = K₁ ⊓ T ∧
    normalizer (T : Set G) ≤
      ((K₁ ⊔ conjSub z K₁) ⊔ AltStdSec.oddCoreOf (normalizer (T : Set G))) ⊔ zpowers z ∧
    (K₁ ⊔ conjSub z K₁) ⊓ AltStdSec.oddCoreOf (normalizer (T : Set G)) = ⊥

end Config

section Steps

@[expose] def Sec4FusionN0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G) (c : Config G L Q n θ z),
      ∃ g ∈ N0 θ c.hn8 z, g * z * g⁻¹ = z * w θ c.hn8

@[expose] def Sec4N0Struct : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G) (c : Config G L Q n θ z),
      (∃ g ∈ N0 θ c.hn8 z, g * z * g⁻¹ = z * w θ c.hn8) → ∃ T : Subgroup G, N0Data θ c.hn8 z T

@[expose] def Sec4N0Elementary : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G) (c : Config G L Q n θ z) (T : Subgroup G),
      N0Data θ c.hn8 z T → ∀ x ∈ T, x ^ 2 = 1

@[expose] def Sec4HSetup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G) (c : Config G L Q n θ z) (T : Subgroup G),
      N0Data θ c.hn8 z T → (∀ x ∈ T, x ^ 2 = 1) → HData θ c.hn8 z T

@[expose] def Sec4HbarCases : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G) (c : Config G L Q n θ z) (T : Subgroup G),
      HData θ c.hn8 z T →
        Nat.card (Hbar T) = 336 ∨ Nat.card (Hbar T) = 1008 ∨ Nat.card (Hbar T) = 56448 ∨
          Nat.card (Hbar T) = 120960 ∨ Nat.card (Hbar T) = 362880

@[expose] def Sec4HbarNotSmall : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G) (c : Config G L Q n θ z) (T : Subgroup G),
      HData θ c.hn8 z T → Nat.card (Hbar T) ≠ 336 ∧ Nat.card (Hbar T) ≠ 1008

@[expose] def Sec4HTwoPart : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G) (c : Config G L Q n θ z) (T : Subgroup G),
      HData θ c.hn8 z T → 2 ^ 11 ∣ Nat.card (normalizer (T : Set G))

@[expose] def Sec4HbarNotSL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G) (c : Config G L Q n θ z) (T : Subgroup G),
      HData θ c.hn8 z T → Nat.card (Hbar T) ≠ 120960 ∧ Nat.card (Hbar T) ≠ 362880

@[expose] def Sec4Wreath49 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G) (c : Config G L Q n θ z) (T : Subgroup G),
      HData θ c.hn8 z T → Nat.card (Hbar T) = 56448 → WreathStruct z T

end Steps

end CFSG.OddStandard.AltStdSmall4
