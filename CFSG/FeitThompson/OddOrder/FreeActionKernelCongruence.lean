module
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Data.Int.ModEq
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.Index

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open MulAction

theorem card_dvd_card_of_forall_stabilizer_eq_bot {A X : Type*} [Group A] [MulAction A X]
    [Finite A] [Finite X] (h : ∀ x : X, stabilizer A x = ⊥) : Nat.card A ∣ Nat.card X := by
  classical
  have := Fintype.ofFinite (orbitRel.Quotient A X)
  have hcard : Nat.card X = Fintype.card (orbitRel.Quotient A X) * Nat.card A := by
    refine (Nat.card_congr (selfEquivSigmaOrbits A X)).trans ?_
    rw [Nat.card_sigma, Finset.sum_congr rfl (g := fun _ => Nat.card A) (fun ω _ => ?_),
      Finset.sum_const, Finset.card_univ, smul_eq_mul]
    have hi := index_stabilizer A ω.out
    rw [h, Subgroup.index_bot] at hi
    rw [Nat.card_coe_set_eq, ← hi]
  exact hcard ▸ Dvd.intro_left _ rfl

variable (A K : Type*) [Group A] [Group K] [MulDistribMulAction A K]

def nonidentitySubMulAction : SubMulAction A K where
  carrier := {k : K | k ≠ 1}
  smul_mem' a k hk := by
    simp only [Set.mem_ofPred_eq] at hk ⊢
    exact fun h => hk (MulAction.injective a (show a • k = a • 1 by rw [h, smul_one]))

@[simp]
theorem mem_nonidentitySubMulAction {k : K} : k ∈ nonidentitySubMulAction A K ↔ k ≠ 1 := Iff.rfl

@[simp]
theorem coe_nonidentitySubMulAction :
    (nonidentitySubMulAction A K : Set K) = {k : K | k ≠ 1} := (rfl)

theorem card_nonidentitySubMulAction [Finite K] :
    Nat.card (nonidentitySubMulAction A K) = Nat.card K - 1 := by
  classical
  have := Fintype.ofFinite K
  have h : Nat.card (nonidentitySubMulAction A K) = Nat.card {k : K // k ≠ 1} := rfl
  rw [h]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (p := fun x : K => x = 1)]

theorem card_dvd_card_sub_one_of_smul_eq_self [Finite A] [Finite K]
    (h : ∀ k : K, k ≠ 1 → ∀ a : A, a • k = k → a = 1) :
    Nat.card A ∣ Nat.card K - 1 := by
  rw [← card_nonidentitySubMulAction A K]
  refine card_dvd_card_of_forall_stabilizer_eq_bot fun x => ?_
  ext a
  simp only [Subgroup.mem_bot, mem_stabilizer_iff]
  refine ⟨fun ha => h x.1 ((mem_nonidentitySubMulAction A K).1 x.2) a
    (congrArg Subtype.val ha), ?_⟩
  rintro rfl
  exact one_smul _ _

theorem card_modEq_one_of_smul_eq_self [Finite A] [Finite K]
    (h : ∀ k : K, k ≠ 1 → ∀ a : A, a • k = k → a = 1) :
    (Nat.card K : ℤ) ≡ 1 [ZMOD (Nat.card A : ℤ)] := by
  have hd := card_dvd_card_sub_one_of_smul_eq_self A K h
  have h1 : 1 ≤ Nat.card K := Nat.card_pos
  have hz : (Nat.card A : ℤ) ∣ (Nat.card K : ℤ) - 1 := by
    have h' := Int.natCast_dvd_natCast.2 hd
    rwa [Nat.cast_sub h1, Nat.cast_one] at h'
  exact Int.modEq_iff_dvd.2 (dvd_sub_comm.1 hz)

end CFSG.FeitThompson
