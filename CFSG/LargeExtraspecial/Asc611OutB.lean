module

public import CFSG.LargeExtraspecial.Asc611OutA

public section

namespace CFSG.LargeExtraspecial.Asc611

open Subgroup Matrix CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

structure SemiInv (S : (Fin m → K) → Fin m → K) : Prop where
  add : ∀ x y, S (x + y) = S x + S y
  smul : ∀ (c : K) x, S (c • x) = frob c • S x
  herm_eq : ∀ x y, herm frob (S x) (S y) = frob (herm frob x y)
  invol : ∀ x, S (S x) = x

theorem frob_mul_self_of_mem {c : K} (hc : c = 0 ∨ c = 1) : frob c * c = c := by
  rcases hc with rfl | rfl <;> simp

namespace SemiInv

variable {S : (Fin m → K) → Fin m → K} (hS : SemiInv S)
include hS

theorem zero : S 0 = 0 := by
  have h := hS.smul 0 0
  rwa [zero_smul, map_zero, zero_smul] at h

theorem fix_add_self (x : Fin m → K) : S (x + S x) = x + S x := by
  rw [hS.add, hS.invol, add_comm]

theorem decomp (x : Fin m → K) :
    x = frob ω • (x + S x) + (ω • x + S (ω • x)) := by
  rw [hS.smul, smul_add, add_add_add_comm, ← add_smul, ← add_smul, add_comm (frob ω) ω,
    omega_add_frob, one_smul, add_self_K, zero_smul, add_zero]

theorem herm_fix {x y : Fin m → K} (hx : S x = x) (hy : S y = y) :
    herm frob x y = 0 ∨ herm frob x y = 1 := by
  have h := hS.herm_eq x y
  rw [hx, hy] at h
  exact (frob_eq_self_iff _).mp h.symm

theorem eq_zero_of_herm {d : Fin m → K} (hd : ∀ x, S x = x → herm frob x d = 0) : d = 0 := by
  have hall : ∀ v, herm frob v d = 0 := by
    intro v
    rw [hS.decomp v, herm_add_left, herm_smul_left, hd _ (hS.fix_add_self v),
      hd _ (hS.fix_add_self _), mul_zero, add_zero]
  funext i
  have h := hall (Pi.single i 1)
  rwa [herm_single_left, map_one, one_mul] at h

theorem eq_of_fix {g g' : SUid frob m} (h : ∀ x, S x = x → g • x = g' • x) : g = g' := by
  have key : ∀ (k : SUid frob m) (c : K) (a b : Fin m → K), k • (c • a + b) = c • (k • a) + k • b :=
    fun k c a b => by rw [smul_add, smul_smul_comm]
  refine ext_smul _ fun v => ?_
  calc g • v = g • (frob ω • (v + S v) + (ω • v + S (ω • v))) := by rw [← hS.decomp v]
    _ = frob ω • (g • (v + S v)) + g • (ω • v + S (ω • v)) := key g _ _ _
    _ = frob ω • (g' • (v + S v)) + g' • (ω • v + S (ω • v)) := by
        rw [h _ (hS.fix_add_self v), h _ (hS.fix_add_self _)]
    _ = g' • (frob ω • (v + S v) + (ω • v + S (ω • v))) := (key g' _ _ _).symm
    _ = g' • v := by rw [← hS.decomp v]

end SemiInv

theorem semiInv_of_realize (hm : 4 ≤ m) {β : MulAut (PG m)} (hββ : β * β = 1)
    {A : primeFormUnitary AS35U.hF ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)}
    {φ : K ≃+* K} (hβ : ∀ g : SUid frob m, ∃ g' : SUid frob m,
      (g' : GL (Fin m) K) = (A : GL (Fin m) K) * glAut φ g * (A : GL (Fin m) K)⁻¹ ∧
        β (QuotientGroup.mk g) = QuotientGroup.mk g') (hφ : ∀ c, φ c = frob c) :
    SemiInv (AS35K.semi (A : GL (Fin m) K) φ) where
  add := AS35K.semi_add _ _
  smul c x := by rw [AS35K.semi_smul, hφ]
  herm_eq x y := by rw [AS35K.herm_semi A.2, hφ]
  invol := semi_semi_eq hm hββ hβ hφ

end CFSG.LargeExtraspecial.Asc611
