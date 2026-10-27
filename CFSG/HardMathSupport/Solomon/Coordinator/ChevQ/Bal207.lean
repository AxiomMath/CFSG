module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Defs
public import CFSG.HardMathSupport.Dickson.I271.Support.EngineBasic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Dickson.I271

open scoped commutatorElement

namespace Bal207Aux

@[expose] def IsSpIdx : TauCeti.LieTypeIndex → Prop
  | .B _ _ => True
  | _ => False

@[expose] def IsUniIdx : TauCeti.LieTypeIndex → Prop
  | .twistedA r q => ¬ 3 ∣ r + 1 ∧ (IsTwoPow q 1 ∨ IsTwoPow q 3)
  | _ => False

@[expose] def IsOrthIdx : TauCeti.LieTypeIndex → Prop
  | .D _ _ => True
  | .twistedD _ _ => True
  | _ => False

@[expose] def IsSuzuki2Index : TauCeti.LieTypeIndex → Prop
  | .suzuki m => m = 2
  | _ => False

@[expose] def IsSmallTwistedIdx : TauCeti.LieTypeIndex → Prop
  | .twistedA r q => r = 2 ∧ ((q.p = 3 ∧ q.exponent = 1) ∨ IsTwoPow q 3)
  | _ => False

@[expose] def IsBalSmall {X : Type} [Group X] (J : Subgroup X) : Prop :=
  Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* ↥(alternatingGroup (Fin 6))) ∨
    IsLieQuot ↥J IsSmallTwistedIdx ∨ IsLieQuot ↥J IsL2EightIndex

abbrev FamSp (p : ℕ) (d : TauCeti.LieTypeIndex) : Prop := Bal207Index p d ∧ IsSpIdx d

abbrev FamUni (p : ℕ) (d : TauCeti.LieTypeIndex) : Prop := Bal207Index p d ∧ IsUniIdx d

abbrev FamOrth (p : ℕ) (d : TauCeti.LieTypeIndex) : Prop := Bal207Index p d ∧ IsOrthIdx d

abbrev FamExc (p : ℕ) (d : TauCeti.LieTypeIndex) : Prop :=
  Bal207Index p d ∧ ¬ IsSpIdx d ∧ ¬ IsUniIdx d ∧ ¬ IsOrthIdx d

theorem not_mem_centralizer_of_inf_eq_bot {X : Type} [Group X] {K A : Subgroup X}
    (hdisj : A ⊓ Subgroup.centralizer (K : Set X) = ⊥) {a : X} (ha : a ∈ A) (ha1 : a ≠ 1) :
    a ∉ Subgroup.centralizer (K : Set X) := by
  intro h
  have h' : a ∈ A ⊓ Subgroup.centralizer (K : Set X) := ⟨ha, h⟩
  rw [hdisj, Subgroup.mem_bot] at h'
  exact ha1 h'

theorem card_centralizer_singleton_lt {X : Type} [Group X] [Finite X] {K : Subgroup X} {a : X}
    (ha : a ∉ Subgroup.centralizer (K : Set X)) :
    Nat.card ↥(Subgroup.centralizer ({a} : Set X)) < Nat.card X := by
  have hne : Subgroup.centralizer ({a} : Set X) ≠ ⊤ := by
    intro htop
    apply ha
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hkt : k ∈ Subgroup.centralizer ({a} : Set X) := by
      rw [htop]
      exact Subgroup.mem_top k
    rw [Subgroup.mem_centralizer_iff] at hkt
    exact (hkt a (Set.mem_singleton a)).symm
  have h1 := Subgroup.card_mul_index (Subgroup.centralizer ({a} : Set X))
  have h2 : (Subgroup.centralizer ({a} : Set X)).index ≠ 1 :=
    fun h => hne (Subgroup.index_eq_one.1 h)
  have h3 : (Subgroup.centralizer ({a} : Set X)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h4 : 0 < Nat.card ↥(Subgroup.centralizer ({a} : Set X)) := Nat.card_pos
  have h5 : 2 ≤ (Subgroup.centralizer ({a} : Set X)).index := by omega
  nlinarith

end Bal207Aux

open Bal207Aux

@[expose] def Bal207Clauses {X : Type} [Group X] (p : ℕ) (K B A : Subgroup X) : Prop :=
  (∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
        B ≤ Subgroup.normalizer (J : Set X) ∧ IsStronglyLocallyOneBalanced p B a J) ∧
  (∃ a ∈ A, a ≠ 1 ∧ ∀ w ∈ Subgroup.normalizer (K : Set X), Nat.Coprime p (orderOf w) →
      (∀ b ∈ B, ⁅w, b⁆ ∈ Subgroup.centralizer (K : Set X)) →
        ∀ J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
          w ∈ Subgroup.normalizer (J : Set X))

@[expose] def Bal207Dvd : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K : Subgroup X), p.Prime →
    CFSG.Open.IsComponentOf K ⊤ → IsLieQuot ↥K (Bal207Index p) → p ∣ Nat.card ↥K

@[expose] def Bal207LocalBal : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (p : ℕ) (K A : Subgroup X),
    p.Prime → p ≠ 2 → CFSG.Open.IsComponentOf K ⊤ → IsLieQuot ↥K (Bal207Index p) →
      A ≤ Subgroup.normalizer (K : Set X) → CFSG.Open.IsElemAbelian p A →
        IsCompLocallyBalanced p 1 A K

@[expose] def Bal207Rank : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (p : ℕ) (K B : Subgroup X),
    p.Prime → p ≠ 2 → CFSG.Open.IsComponentOf K ⊤ → IsSCp p ⊤ B →
      B ≤ Subgroup.normalizer (K : Set X) → IsLieQuot ↥K (Bal207Index p) →
        (∃ A : Subgroup X, A ≤ B ∧ ¬ IsCyclic ↥A ∧ A ⊓ Subgroup.centralizer (K : Set X) = ⊥ ∧
          A ⊔ (B ⊓ Subgroup.centralizer (K : Set X)) = B) ∨
        (p = 5 ∧ IsLieQuot ↥K IsSuzuki2Index ∧
          ∀ A : Subgroup X, A ≤ B → A ⊓ Subgroup.centralizer (K : Set X) = ⊥ →
            A ⊔ (B ⊓ Subgroup.centralizer (K : Set X)) = B → IsCyclic ↥A)

@[expose] def Bal207SzCyclic : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (K B : Subgroup X),
    CFSG.Open.IsComponentOf K ⊤ → IsSCp 5 ⊤ B → B ≤ Subgroup.normalizer (K : Set X) →
      IsLieQuot ↥K IsSuzuki2Index →
        (∀ A : Subgroup X, A ≤ B → A ⊓ Subgroup.centralizer (K : Set X) = ⊥ →
          A ⊔ (B ⊓ Subgroup.centralizer (K : Set X)) = B → IsCyclic ↥A) →
            IsStronglyBalancedIn 5 B K

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
