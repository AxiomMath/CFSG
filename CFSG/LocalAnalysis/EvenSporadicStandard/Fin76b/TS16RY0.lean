module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.RootFacts

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

@[expose] def fixedSub {X : Type*} [Group X] (r : MulAut X) : Subgroup X where
  carrier := {x | r x = x}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

theorem mem_fixedSub {X : Type*} [Group X] {r : MulAut X} {x : X} :
    x ∈ fixedSub r ↔ r x = x := Iff.rfl

@[expose] def thetaSub {X : Type*} [Group X] (t : X) (r : MulAut X) : Subgroup (MulAut X) :=
  (centralizer ({t} : Set X)).map (MulAut.conj : X →* MulAut X) ⊔ zpowers r

@[expose] def quadSet {X : Type*} [Group X] (t ξ : X) : Set (MulAut X) :=
  {1, MulAut.conj t, MulAut.conj ξ, MulAut.conj t * MulAut.conj ξ}

structure S16Rel {X : Type*} [Group X] (t β : X) (r : MulAut X) (v ξ : X) : Prop where
  r_sq : r * r = 1
  r_outer : ¬ IsInnerAut r
  r_t : r t = t
  r_β : r β = β⁻¹
  v_t : v * t = t * v
  ξ_t : ξ * t = t * ξ
  v4 : v ^ 4 = t
  v8 : v ^ 8 = 1
  ξ_sq : ξ * ξ = 1
  ξ_ne_one : ξ ≠ 1
  ξ_ne_t : ξ ≠ t
  ξ_v : ξ * v * ξ⁻¹ = v⁻¹
  r_v : r v = v * t
  r_ξ : r ξ = ξ * t
  v_β : v * β * v⁻¹ = β⁻¹
  ξ_β : ξ * β * ξ⁻¹ = β⁻¹
  card_CE : Nat.card ↥(rootGroup X t ⊓ fixedSub r) = 8
  CE_eq : closure ({v * v, v * ξ} : Set X) = rootGroup X t ⊓ fixedSub r
  card_Y : Nat.card ↥(closure ({MulAut.conj v, MulAut.conj ξ, r} : Set (MulAut X))) = 32
  rank5 : ∃ C : Subgroup (MulAut X), C ≤ thetaSub t r ∧ MulAut.conj t ∈ C ∧
    MulAut.conj ξ ∈ C ∧ C ≤ centralizer ({MulAut.conj ξ} : Set (MulAut X)) ∧ Nat.card ↥C = 32 ∧
    (∀ c ∈ C, c * c ∈ quadSet t ξ) ∧ ∀ c ∈ C, ∀ d ∈ C, c * d * c⁻¹ * d⁻¹ ∈ quadSet t ξ

@[expose] def S16Model (X : Type*) [Group X] (t β : X) : Prop :=
  ∃ (r : MulAut X) (v ξ : X), S16Rel t β r v ξ

end CFSG.EvenSporadicStandard.Fin76b
