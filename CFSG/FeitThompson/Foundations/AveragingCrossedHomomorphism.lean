module

public import CFSG.FeitThompson.Foundations.DivisionCoprimeToAbelianOrder
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {A : Type*} [AddCommGroup A]

section

variable {Q : Type*} [Fintype Q]

noncomputable def crossedHomAverage (h : (Nat.card Q).Coprime (Nat.card A)) (f : Q → A) : A :=
  (nsmulCoprimeAddAut h).symm (∑ y, f y)

@[simp]
theorem nsmul_crossedHomAverage (h : (Nat.card Q).Coprime (Nat.card A)) (f : Q → A) :
    Nat.card Q • crossedHomAverage h f = ∑ y, f y :=
  nsmul_nsmulCoprimeAddAut_symm h _

theorem crossedHomAverage_eq_iff (h : (Nat.card Q).Coprime (Nat.card A)) (f : Q → A) (v : A) :
    crossedHomAverage h f = v ↔ Nat.card Q • v = ∑ y, f y := by
  refine ⟨fun hv => by rw [← hv, nsmul_crossedHomAverage], fun hv => ?_⟩
  rw [crossedHomAverage, ← hv, nsmulCoprimeAddAut_symm_nsmul]

variable [Group Q] [DistribMulAction Q A]

theorem sum_eq_nsmul_add_smul_sum (f : Q → A) (hf : ∀ x y : Q, f (x * y) = f x + x • f y) (x : Q) :
    ∑ y, f y = Nat.card Q • f x + x • ∑ y, f y := by
  calc ∑ y, f y = ∑ y : Q, f (x * y) := (Equiv.sum_comp (Equiv.mulLeft x) f).symm
    _ = ∑ y : Q, (f x + x • f y) := by simp [hf]
    _ = Nat.card Q • f x + x • ∑ y, f y := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← Finset.smul_sum,
          Nat.card_eq_fintype_card]

theorem eq_sub_smul_of_nsmul_eq_sum (h : (Nat.card Q).Coprime (Nat.card A)) (f : Q → A)
    (hf : ∀ x y : Q, f (x * y) = f x + x • f y) {v : A} (hv : Nat.card Q • v = ∑ y, f y) (x : Q) :
    f x = v - x • v := by
  refine (Nat.Coprime.nsmul_right_bijective (G := A) (n := Nat.card Q) h.symm).injective ?_
  rw [smul_sub, smul_comm, hv, eq_sub_iff_add_eq]
  exact (sum_eq_nsmul_add_smul_sum f hf x).symm

theorem crossedHom_eq_sub_smul_crossedHomAverage (h : (Nat.card Q).Coprime (Nat.card A))
    (f : Q → A) (hf : ∀ x y : Q, f (x * y) = f x + x • f y) (x : Q) :
    f x = crossedHomAverage h f - x • crossedHomAverage h f :=
  eq_sub_smul_of_nsmul_eq_sum h f hf (nsmul_crossedHomAverage h f) x

end

theorem exists_forall_crossedHom_eq_sub_smul {Q : Type*} [Group Q] [Finite Q]
    [DistribMulAction Q A] (h : (Nat.card Q).Coprime (Nat.card A)) (f : Q → A)
    (hf : ∀ x y : Q, f (x * y) = f x + x • f y) : ∃ v : A, ∀ x : Q, f x = v - x • v := by
  have : Fintype Q := Fintype.ofFinite Q
  exact ⟨crossedHomAverage h f, crossedHom_eq_sub_smul_crossedHomAverage h f hf⟩

end

end CFSG.FeitThompson
