module

public import CFSG.Open.Catalog
public import CFSG.GH74.GLS.Pattern

public section

namespace CFSG.GH74.GLS.Bg

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def B_reciprocity : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (x y : G), orderOf x = 2 →
    orderOf y = 2 → Commute x y → ∀ (L J : Subgroup G),
    (IsPCompIn 2 (centralizer ({x} : Set G)) L ∧ pRank 2 ↥L = 1 ∧ x ∈ L) →
    (IsPCompIn 2 (centralizer ({y} : Set G)) J ∧ pRank 2 ↥J = 1 ∧ y ∈ J) →
      (x ∈ normalizer (J : Set G) → y ∈ normalizer (L : Set G)) ∧
      (x ∈ normalizer (J : Set G) → ∀ a ∈ J, IsPGroup 2 (zpowers a) → a ∉ zpowers y →
        Commute a x → a ∈ normalizer (L : Set G))

@[expose] def B_pu5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → 3 ≤ pRank 2 G → ∀ z : G,
    orderOf z = 2 → z ∈ rigidProduct z → IsStronglyClassicalInvolution G z

@[expose] def B_iii2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → 3 ≤ pRank 2 G →
    ∀ (x : G) (K : Subgroup G), IsTwoTerminal x K → pRank 2 ↥K = 1 →
      ∃ (x' : G) (K' : Subgroup G), IsPRigid 2 x' K' ∧ pRank 2 ↥K' = 1 ∧ x' ∈ rigidProduct x' ∧
        ∃ t ∈ centralizer ({x'} : Set G), IsConj x' t ∧ t ∉ zStar (rigidProduct x')

section Bender

variable {G : Type} [Group G]

@[expose] def Fm (M : Subgroup G) : Subgroup G := inSubgroup (fun K _ => fittingSubgroup K) M

@[expose] def Fs (M : Subgroup G) : Subgroup G := inSubgroup (fun K _ => generalizedFitting K) M

@[expose] def Em (M : Subgroup G) : Subgroup G := inSubgroup (fun K _ => layer K) M

@[expose] def Op (p : ℕ) (M : Subgroup G) : Subgroup G := inSubgroup (pCore p) M

@[expose] def Fpi (σ : Set ℕ) (N : Subgroup G) : Subgroup G := ⨆ p ∈ σ, Op p (Fm N)

@[expose] def Links (M N : Subgroup G) : Prop :=
  ∃ Y : Subgroup G, Y ≤ Fm M ∧ (Fs M ⊓ normalizer (Y : Set G)) ≤ N

end Bender

@[expose] def B_bender_lemma_1_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (M N : Subgroup G), IsCoatom M → ∀ Y : Subgroup G,
    Y ≤ Fm M → Fs M ⊓ normalizer (Y : Set G) ≤ N →
      (Fpi {p | p.Prime ∧ ¬ p ∣ Nat.card (Fm M)} N ⊓ M = ⊥) ∧
      ((∃ p : ℕ, p.Prime ∧ IsPGroup p (Fs M)) ∨ Fpi {p | p.Prime ∧ p ∣ Nat.card (Fm M)} N ≤ M) ∧
      ∀ p : ℕ, p.Prime → p ∣ Nat.card (Fm M) →
        ⁅inSubgroup (oResidual p) (Fs M ⊓ normalizer (Y : Set G)), Op p N⁆ = ⊥

@[expose] def B_bender_1_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (M N : Subgroup G), IsCoatom M → IsCoatom N →
    Links M N → Links N M → M = N ∨ ∃ p : ℕ, p.Prime ∧ IsPGroup p (Fs M) ∧ IsPGroup p (Fs N)

@[expose] def B_bender_1_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (M N : Subgroup G), IsCoatom M → IsCoatom N →
    Links M N → (¬ ∃ p : ℕ, p.Prime ∧ IsPGroup p (Fs M)) →
      (Links N M → M = N) ∧ ∀ g : G, N = conjugate M g → Em M = ⊥ → g ∈ M

@[expose] def B_signalizer_19_9 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (z : X), orderOf z = 2 → ∀ r : ℕ, r.Prime → r ≠ 2 →
    ∀ R : Subgroup X, IsPGroup r R → (∀ c ∈ centralizer ({z} : Set X), c ∈ normalizer (R : Set X)) →
      ⁅R, zpowers z⁆ = R →
      (∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ r → R ≤ centralizer ((pCore p X : Subgroup X) : Set X)) ∧
      (R ≤ pPrimeCore 2 X → R ≤ pCore r X)

section KInfty

variable {G : Type*} [Group G]

@[expose] def classTwo (P : Subgroup G) : Set (Subgroup G) := {B | B ≤ P ∧ ⁅⁅B, B⁆, B⁆ = ⊥}

@[expose] def zOf (B : Subgroup G) : Subgroup G := B ⊓ centralizer (B : Set G)

@[expose] def Klow (P Q : Subgroup G) : Set (Subgroup G) :=
  {B | B ∈ classTwo P ∧ Q ≤ normalizer (B : Set G) ∧
    ∀ A ∈ classTwo P, A ≤ Q → B ≤ normalizer (A : Set G) →
      ⁅B, ⁅A, A⁆⁆ = ⊥ → ⁅⁅zOf B, A⁆, A⁆ = ⊥ → ⁅B, A⁆ ≤ zOf B}

@[expose] def Kup (P Q : Subgroup G) : Set (Subgroup G) :=
  {B | B ∈ classTwo P ∧ ⁅B, Q⁆ ≤ zOf B}

@[expose] def gen (S : Set (Subgroup G)) : Subgroup G := Subgroup.closure (⋃ B ∈ S, (B : Set G))

@[expose] noncomputable def Kfam (P : Subgroup G) : ℕ → Set (Subgroup G)
  | 0 => classTwo P
  | (n + 1) => if Even n then Klow P (gen (Kfam P n)) else Kup P (gen (Kfam P n))

@[expose] def kInfty (P : Subgroup G) : Subgroup G := gen (⋂ i : ℕ, Kfam P (2 * i))

@[expose] def kLowInfty (P : Subgroup G) : Subgroup G := gen (⋃ i : ℕ, Kfam P (2 * i + 1))

end KInfty

@[expose] def B_normal_Ep2 : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (P : Type) [Group P] [Finite P], IsPGroup p P →
    ∀ Q : Subgroup P, Q.Normal → 2 ≤ pRank p Q →
      (∃ E : Subgroup P, E.Normal ∧ E ≤ Q ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ 2) ∨
      (p = 2 ∧ ((∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥Q ≃* DihedralGroup (2 ^ m))) ∨
        ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥Q ≃* CFSG.Open.SemidihedralGroup n)))

@[expose] def B_maximalClass_of_small_centralizer : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (P : Type) [Group P] [Finite P], IsPGroup p P → p ^ 3 ≤ Nat.card P →
    ∀ x : P, Nat.card (centralizer ({x} : Set P)) ≤ p ^ 2 →
      ∃ m : ℕ, Nat.card P = p ^ m ∧ (⊤ : Subgroup P).lowerCentralSeries (m - 2) ≠ ⊥

@[expose] def B_two_maximalClass_shape : Prop :=
  ∀ (P : Type) [Group P] [Finite P], IsPGroup 2 P → 8 < Nat.card P →
    ∀ m : ℕ, Nat.card P = 2 ^ m → (⊤ : Subgroup P).lowerCentralSeries (m - 2) ≠ ⊥ →
      (∃ k : ℕ, 1 ≤ k ∧ Nonempty (P ≃* DihedralGroup (2 ^ k))) ∨
      (∃ k : ℕ, 1 ≤ k ∧ Nonempty (P ≃* QuaternionGroup (2 ^ k))) ∨
      ∃ n : ℕ, 4 ≤ n ∧ Nonempty (P ≃* CFSG.Open.SemidihedralGroup n)

end CFSG.GH74.GLS.Bg
