module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerHyp
public import Mathlib.Algebra.Group.MinimalAxioms

public section

namespace CFSG.OddStandard.AltStdSmall4.Tower

open Subgroup

structure ExtData (K : Type*) [Group K] where
  α : MulAut K
  g : K
  hαg : α g = g
  hα2 : ∀ k, α (α k) = g * k * g⁻¹

variable {K : Type*} [Group K]

@[ext] structure CycExt (D : ExtData K) where
  k : K
  d : Bool

namespace CycExt

variable (D : ExtData K)

@[expose] def pw (d : Bool) (k : K) : K := if d then D.α k else k

@[expose] def sq (d d' : Bool) : K := if d && d' then D.g else 1

instance : Mul (CycExt D) := ⟨fun a b => ⟨a.k * pw D a.d b.k * sq D a.d b.d, xor a.d b.d⟩⟩

instance : One (CycExt D) := ⟨⟨1, false⟩⟩

instance : Inv (CycExt D) :=
  ⟨fun a => if a.d then ⟨D.g⁻¹ * (D.α a.k)⁻¹, true⟩ else ⟨a.k⁻¹, false⟩⟩

theorem mk_mul_mk (k k' : K) (d d' : Bool) :
    (⟨k, d⟩ * ⟨k', d'⟩ : CycExt D) = ⟨k * pw D d k' * sq D d d', xor d d'⟩ := rfl

theorem one_def : (1 : CycExt D) = ⟨1, false⟩ := rfl

theorem inv_mk_true (k : K) : (⟨k, true⟩ : CycExt D)⁻¹ = ⟨D.g⁻¹ * (D.α k)⁻¹, true⟩ := rfl

theorem inv_mk_false (k : K) : (⟨k, false⟩ : CycExt D)⁻¹ = ⟨k⁻¹, false⟩ := rfl

instance : Group (CycExt D) := Group.ofLeftAxioms
  (fun a b c => by
    obtain ⟨k₁, d₁⟩ := a
    obtain ⟨k₂, d₂⟩ := b
    obtain ⟨k₃, d₃⟩ := c
    cases d₁ <;> cases d₂ <;> cases d₃ <;>
      simp only [mk_mul_mk, pw, sq, map_mul, map_one, D.hαg, D.hα2, Bool.and_true,
        Bool.and_false, Bool.true_and, Bool.false_and, Bool.xor_true, Bool.xor_false,
        Bool.not_true, Bool.not_false, ite_true, ite_false, Bool.false_eq_true, mul_one,
        CycExt.mk.injEq, and_true] <;> group)
  (fun a => by
    obtain ⟨k, d⟩ := a
    cases d <;> simp [one_def, mk_mul_mk, pw, sq])
  (fun a => by
    obtain ⟨k, d⟩ := a
    cases d
    · simp [one_def, inv_mk_false, mk_mul_mk, pw, sq]
    · simp only [one_def, inv_mk_true, mk_mul_mk, pw, sq, ite_true, Bool.and_self,
        Bool.xor_self, CycExt.mk.injEq, and_true]
      group)

@[expose] def incl : K →* CycExt D where
  toFun k := ⟨k, false⟩
  map_one' := rfl
  map_mul' a b := by
    change _ = (⟨a, false⟩ * ⟨b, false⟩ : CycExt D)
    rw [mk_mul_mk]
    simp [pw, sq]

end CycExt

@[expose] def Conj {X : Type*} [Group X] (x t : X) : Prop := ∃ k, x = k * t * k⁻¹

@[expose] def IsPInv {X : Type*} [Group X] (x : X) : Prop :=
  x ^ 2 = 1 ∧ x ≠ 1 ∧ PInv (centralizer {x} : Subgroup X)

@[expose] def L3Facts (X : Type*) [Group X] (t : X) : Prop :=
  ∃ Q : Subgroup X, Q.index = 2 ∧ t ∉ Q ∧ ∀ x, IsPInv x → Conj x t

@[expose] def L2Facts (X : Type*) [Group X] (t : X) : Prop :=
  ∃ Q : Subgroup X, Q.index = 2 ∧ t ∉ Q ∧ (∀ x ∈ Q, ¬IsPInv x) ∧
    ∃ x₀ : X, (∀ x, IsPInv x → Conj x t ∨ Conj x x₀) ∧
      (Conj x₀ t ∨ ∀ D : ExtData X, D.α x₀ = t →
        Nat.card (centralizer {CycExt.incl D t} : Subgroup (CycExt D)) = 2 ^ 8 →
          L3Facts (CycExt D) (CycExt.incl D t))

@[expose] def L1Facts (X : Type*) [Group X] (t : X) : Prop :=
  Nat.card (centralizer {t} : Subgroup X) = 2 ^ 7 ∧ ∃ Q : Subgroup X, Q.index = 2 ∧ t ∉ Q ∧
    (∀ x ∈ Q, x ^ 2 = 1 → x ≠ 1 → 2 ^ 8 ≤ Nat.card (centralizer {x} : Subgroup X) ∧
      ¬PInv (centralizer {x} : Subgroup X)) ∧
    ∀ x ∉ Q, x ^ 2 = 1 → Conj x t

@[expose] def TowerFacts (X : Type*) [Group X] (t : X) : Prop :=
  L1Facts X t ∧ ∀ D : ExtData X, D.α t = t → D.g * t = t * D.g →
    PInv (centralizer {CycExt.incl D t} : Subgroup (CycExt D)) →
      L2Facts (CycExt D) (CycExt.incl D t)

end CFSG.OddStandard.AltStdSmall4.Tower
