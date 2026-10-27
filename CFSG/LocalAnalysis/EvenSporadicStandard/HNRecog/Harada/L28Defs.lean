module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

variable {X : Type} [Group X]

structure L28Hyp (A : Subgroup X) (w : X) (ψ : ↥(normalizer (A : Set X)) →* A5WrTwo) :
    Prop where
  elemAb : IsElemAbelian 2 A
  card : Nat.card A = 2 ^ 8
  surj : Function.Surjective ψ
  ker : ψ.ker = A.subgroupOf (normalizer (A : Set X))
  faithful : ∀ x ∈ normalizer (A : Set X), (∀ a ∈ A, x * a = a * x) → x ∈ A
  w_mem : w ∈ A
  w_ne_one : w ≠ 1
  stab : Nonempty (↥(Subgroup.map ψ (centralizer
    ({(⟨w, Subgroup.le_normalizer w_mem⟩ : ↥(normalizer (A : Set X)))} :
      Set ↥(normalizer (A : Set X))))) ≃* Equiv.Perm (Fin 5))

structure Abs210 (A : Subgroup X) (w : X) (ψ : ↥(normalizer (A : Set X)) →* A5WrTwo) : Prop
    extends L28Hyp A w ψ where
  outer : ∃ v : ↥(normalizer (A : Set X)), (v : X) ∉ A ∧ (v : X) * (v : X) = 1 ∧
    ψ v ∉ commutator A5WrTwo ∧ Nat.card ↥(A ⊓ centralizer ({(v : X)} : Set X)) ≤ 16
  invol : ∃ q : ↥(normalizer (A : Set X)), (q : X) ∉ A ∧ (q : X) * (q : X) = 1 ∧
    ψ q ∈ commutator A5WrTwo
  odd : ∀ P : Subgroup X, P.Normal → Odd (Nat.card P) → P = ⊥
  noA5 : ∀ D : Subgroup X, D ≤ normalizer (A : Set X) → (∀ d ∈ D, d * w = w * d) →
    IsEmpty (↥D ≃* alternatingGroup (Fin 5))

end CFSG.EvenSporadicStandard.HNRecog.Harada
