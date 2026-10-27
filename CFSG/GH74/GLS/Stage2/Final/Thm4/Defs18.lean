module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Vocab

variable {G : Type} [Group G]

@[expose] def omega1Z (p : ℕ) (P : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ P ∧ (∀ y ∈ P, x * y = y * x) ∧ x ^ p = 1}
  one_mem' := ⟨one_mem _, fun y _ => by simp, one_pow _⟩
  mul_mem' := by
    rintro a b ⟨haP, hac, hap⟩ ⟨hbP, hbc, hbp⟩
    refine ⟨mul_mem haP hbP, fun y hy => ?_, ?_⟩
    · rw [mul_assoc, hbc y hy, ← mul_assoc, hac y hy, mul_assoc]
    · rw [Commute.mul_pow (hac b hbP), hap, hbp, one_mul]
  inv_mem' := by
    rintro a ⟨haP, hac, hap⟩
    refine ⟨inv_mem haP, fun y hy => ?_, by rw [inv_pow, hap, inv_one]⟩
    exact (Commute.inv_left (hac y hy)).eq

@[expose] def piF (M : Subgroup G) : Set ℕ := {r | r.Prime ∧ r ∣ Nat.card ↥(Fm M)}

@[expose] def piF' (M : Subgroup G) : Set ℕ := {r | r.Prime ∧ ¬ r ∣ Nat.card ↥(Fm M)}

@[expose] def Vof (M E : Subgroup G) : Subgroup G := Fm M ⊓ centralizer (E : Set G)

@[expose] def Dstar (M D : Subgroup G) : Set G :=
  {d | d ∈ D ∧ d ≠ 1 ∧ ¬ centralizer ({d} : Set G) ≤ M}

@[expose] def Qof (p : ℕ) (M U : Subgroup G) : Subgroup G := Op p M ⊓ centralizer (U : Set G)

@[expose] def Fof (p : ℕ) (M U : Subgroup G) : Subgroup G :=
  Qof p M U ⊔ Fpi {r | r.Prime ∧ r ≠ 2 ∧ r ≠ p} M

end Vocab

structure Fail17 (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) : Prop where
  ctx : Ctx17 G z k S M
  fail : ¬ Thm4Concl z k S M

structure Ctx18 (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ)
    (E : Subgroup G) (t : G) : Prop where
  base : Fail17 G z k S M
  prime : p.Prime
  odd : p ≠ 2
  rank : 3 ≤ pRank p ↥(Op p M)
  t_mem : t ∈ Op p M
  t_ord : orderOf t = p
  t_rank : 3 ≤ pRank p ↥(Op p M ⊓ centralizer ({t} : Set G))
  t_fail : ¬ centralizer ({t} : Set G) ≤ M
  E_le : E ≤ Op p M
  E_elem : IsElementaryAbelian p ↥E
  t_E : t ∈ E
  E_rank : 3 ≤ pRank p ↥E

structure CtxP (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ) : Prop where
  base : Fail17 G z k S M
  prime : p.Prime
  odd : p ≠ 2
  rank : 3 ≤ pRank p ↥(Op p M)

structure Ctx19 (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ)
    (U : Subgroup G) (t : G) : Prop where
  base : CtxP G z k S M p
  U_le : U ≤ Op p M
  U_normal : (U.subgroupOf (Op p M)).Normal
  U_elem : IsElementaryAbelian p ↥U
  U_card : Nat.card ↥U = p ^ 2
  t_conj : IsConj z t
  t_mem : t ∈ S
  t_ne : t ≠ z

end CFSG.GH74.GLS.Stage2.Final.Thm4
