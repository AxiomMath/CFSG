module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

@[expose] def IG_11_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → ∀ (A B P : Subgroup G),
    IsPGroup p ↥P → IsPGroup p ↥B → Nat.Coprime p (Nat.card ↥A) →
    A ≤ normalizer (P : Set G) → B ≤ normalizer (P : Set G) → (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
    A ≤ centralizer ((P ⊓ centralizer (B : Set G) : Subgroup G) : Set G) → A ≤ centralizer (P : Set G)

@[expose] def IG_11_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → ∀ (X P Q : Subgroup G),
    IsPGroup p ↥P → Nat.Coprime p (Nat.card ↥X) → X ≤ normalizer (P : Set G) →
    X ≤ normalizer (Q : Set G) → Q ≤ P →
    Q ⊔ (P ⊓ centralizer (Q : Set G)) ≤ centralizer (X : Set G) → P ≤ centralizer (X : Set G)

theorem ig_11_8_of (h : IG_11_7) : IG_11_8 := by
  intro G _ _ p hp X P Q hP hX hXP _ hQP hcen
  have hQp : IsPGroup p ↥Q := hP.to_le hQP
  have hXc : X ≤ centralizer ((Q ⊔ (P ⊓ centralizer (Q : Set G)) : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mpr hcen
  have hXQ : X ≤ centralizer (Q : Set G) :=
    Subgroup.le_centralizer_iff.mpr (fun b hb => Subgroup.le_centralizer_iff.mp hXc (Subgroup.mem_sup_left hb))
  have hXC : X ≤ centralizer ((P ⊓ centralizer (Q : Set G) : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mpr (fun b hb => Subgroup.le_centralizer_iff.mp hXc (Subgroup.mem_sup_right hb))
  refine Subgroup.le_centralizer_iff.mp (h G p hp X Q P hP hQp hX hXP (le_trans hQP Subgroup.le_normalizer) ?_ hXC)
  intro a ha b hb
  exact (Subgroup.mem_centralizer_iff.mp (hXQ ha) b hb).symm

@[expose] def IG_11_23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → ∀ (V Y : Subgroup G),
    IsElementaryAbelian p ↥V → Nat.card ↥V = p ^ 2 → Nat.Coprime p (Nat.card ↥Y) →
    V ≤ normalizer (Y : Set G) →
    Y ≤ ⨆ (v : G) (_ : v ∈ V ∧ v ≠ 1), Y ⊓ centralizer ({v} : Set G)

@[expose] def Bender12 : Prop := B_bender_lemma_1_2

@[expose] def Bender13 : Prop := B_bender_1_3

@[expose] def Bender14 : Prop := B_bender_1_4

@[expose] def OddNoncyclicPlane : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (r : ℕ), r.Prime → r ≠ 2 → ∀ R : Subgroup G, IsPGroup r ↥R → ¬ IsCyclic ↥R →
    ∃ V : Subgroup G, V ≤ R ∧ IsElementaryAbelian r ↥V ∧ Nat.card ↥V = r ^ 2

@[expose] def QP_exists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (p : ℕ) (P : Subgroup G), p.Prime → p ≠ 2 → orderOf z = 2 →
    IsPGroup p ↥P → z ∈ normalizer (P : Set G) → ¬ P ≤ centralizer ({z} : Set G) → ∃ Q : Subgroup G, QP z p P Q

end CFSG.GH74.GLS.Stage2.Bender.Thm1
