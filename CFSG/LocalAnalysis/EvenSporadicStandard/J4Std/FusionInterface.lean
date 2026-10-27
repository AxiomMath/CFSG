module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Step3

public section

namespace CFSG.EvenSporadicStandard.J4Std

open Subgroup CFSG.Open CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.M24Std

variable {G : Type} [Group G]

@[expose] def conjSub (g : G) (A : Subgroup G) : Subgroup G := A.map (MulAut.conj g).toMonoidHom

structure RankData (L U : Subgroup G) (z : G) : Prop where
  rank_cent : ∀ B : Subgroup G, (∀ b ∈ B, b * z = z * b) → (∀ b ∈ B, b * b = 1) →
    (∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) → Nat.card B ≤ 2 ^ 12
  conj_E12 : ∀ B : Subgroup G, z ∈ B → (∀ b ∈ B, b * z = z * b) → (∀ b ∈ B, b * b = 1) →
    (∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) → Nat.card B = 2 ^ 12 →
    ∃ l ∈ L, B = conjSub l (Vsub U z)

structure WeakData (U : Subgroup G) (z : G) (Y : Subgroup G) : Prop where
  card_W : Nat.card (Csub U z) = 2 ^ 23
  card_Y : Nat.card Y = 2 ^ 22
  Y_sq : ∀ y ∈ Y, y * y = 1
  Y_comm : ∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y
  cent_Y : ∀ y ∈ Y, y * z = z * y → y ∈ U
  noconj_Y : ∀ g : G, ∀ y ∈ Y, g * z * g⁻¹ ≠ y
  conj_W : ∀ g : G, g * z * g⁻¹ ∈ Csub U z → ∃ u ∈ U, g * z * g⁻¹ = z * u
  z_conj_W : ∀ u ∈ U, ∃ w ∈ Csub U z, w * z * w⁻¹ = z * u
  unique_Y : ∀ A : Subgroup G, A ≤ Csub U z → (∀ a ∈ A, a * a = 1) →
    (∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) → Nat.card A = 2 ^ 22 → A = Y
  sylow_W : ∀ P : Subgroup G, P ≤ centralizer (U : Set G) → IsPGroup 2 P →
    ∃ c ∈ centralizer (U : Set G), P ≤ conjSub c (Csub U z)

structure FusionData (L U : Subgroup G) (z : G) (Y : Subgroup G) : Prop where
  N_le_M : Nsub U z ≤ normalizer (Y : Set G)
  cent_le_N : ∀ m ∈ normalizer (Y : Set G), ∀ y ∈ Y, m * z * m⁻¹ = z * y → m ∈ Nsub U z
  N_eq : ∀ n ∈ Nsub U z, ∃ w ∈ Csub U z, ∃ h ∈ Hloc L U, n = w * h
  fuse : ∀ y ∈ normalizer (Y : Set G), (∃ g : G, g * z * g⁻¹ = y) →
    ∃ m ∈ normalizer (Y : Set G), m * z * m⁻¹ = y

@[expose] def Ega81M24Section : Prop :=
  Ega81HypAZ2A8K → ∀ (X : Type) [Group X] [Finite X], CFSG.SectionRank.IsKGroupCat X →
    ∀ (z : X) (K : Subgroup X), z * z = 1 → z ≠ 1 → IsSporadic K .M24 →
    (∀ k ∈ K, k * z = z * k) →
    (∀ x : X, x * z = z * x → ∃ k ∈ K, x = k ∨ x = k * z) →
    (∃ x : X, x * z * x⁻¹ ≠ z ∧ (x * z * x⁻¹) * z = z * (x * z * x⁻¹)) →
    ∃ E : Subgroup X, E.Normal ∧ E.index = 2 ∧ z ∉ E

end CFSG.EvenSporadicStandard.J4Std
