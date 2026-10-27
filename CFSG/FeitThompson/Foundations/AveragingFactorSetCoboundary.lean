module

public import CFSG.FeitThompson.Foundations.DivisionCoprimeToAbelianOrder
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

section Aux

variable {A : Type*} [AddCommGroup A] {M : Type*} [Monoid M] [DistribMulAction M A] {m : ℕ}

theorem nsmulCoprimeAddAut_symm_smul (h : m.Coprime (Nat.card A)) (x : M) (a : A) :
    (nsmulCoprimeAddAut h).symm (x • a) = x • (nsmulCoprimeAddAut h).symm a := by
  simpa using nsmulCoprimeAddAut_symm_comm h (DistribSMul.toAddMonoidHom A x) a

end Aux

variable {A : Type*} [AddCommGroup A] {Q : Type*} [Group Q] [Fintype Q]

noncomputable def factorSetAverage (h : (Nat.card Q).Coprime (Nat.card A)) (c : Q → Q → A)
    (x : Q) : A :=
  (nsmulCoprimeAddAut h).symm (∑ z, c x z)

omit [Group Q] in
theorem factorSetAverage_apply (h : (Nat.card Q).Coprime (Nat.card A)) (c : Q → Q → A) (x : Q) :
    factorSetAverage h c x = (nsmulCoprimeAddAut h).symm (∑ z, c x z) := (rfl)

theorem nsmul_factorSetAverage (h : (Nat.card Q).Coprime (Nat.card A)) (c : Q → Q → A) (x : Q) :
    Nat.card Q • factorSetAverage h c x = ∑ z, c x z := by
  rw [factorSetAverage_apply, nsmul_nsmulCoprimeAddAut_symm]

theorem eq_factorSetAverage (h : (Nat.card Q).Coprime (Nat.card A)) (c : Q → Q → A) (x : Q) {a : A}
    (ha : Nat.card Q • a = ∑ z, c x z) : a = factorSetAverage h c x := by
  refine (Nat.Coprime.nsmul_right_bijective (G := A) (n := Nat.card Q) h.symm).injective ?_
  rw [ha, nsmul_factorSetAverage]

theorem factorSetAverage_add (h : (Nat.card Q).Coprime (Nat.card A)) (c d : Q → Q → A) (x : Q) :
    factorSetAverage h (fun u v => c u v + d u v) x
      = factorSetAverage h c x + factorSetAverage h d x := by
  rw [factorSetAverage_apply, factorSetAverage_apply, factorSetAverage_apply,
    Finset.sum_add_distrib, map_add]

theorem factorSetAverage_one (h : (Nat.card Q).Coprime (Nat.card A)) {c : Q → Q → A}
    (hc1 : ∀ x, c 1 x = 0) : factorSetAverage h c 1 = 0 := by
  simp [factorSetAverage_apply, hc1]

variable [DistribMulAction Q A]

theorem factorSetAverage_coboundary (h : (Nat.card Q).Coprime (Nat.card A)) {c : Q → Q → A}
    (hcoc : ∀ x y z, c x y + c (x * y) z = x • c y z + c x (y * z)) (x y : Q) :
    c x y = factorSetAverage h c x + x • factorSetAverage h c y
      - factorSetAverage h c (x * y) := by
  have hshift : ∑ z : Q, c x (y * z) = ∑ z : Q, c x z :=
    Fintype.sum_equiv (Equiv.mulLeft y) _ _ fun _ => rfl
  have key : Nat.card Q • c x y = x • (∑ z, c y z) + (∑ z, c x z) - ∑ z, c (x * y) z := by
    have h1 : ∑ z : Q, (c x y + c (x * y) z) = ∑ z : Q, (x • c y z + c x (y * z)) :=
      Finset.sum_congr rfl fun z _ => hcoc x y z
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, ← Finset.smul_sum, hshift] at h1
    rw [eq_sub_iff_add_eq]
    exact h1
  have h2 := congrArg (nsmulCoprimeAddAut h).symm key
  rw [nsmulCoprimeAddAut_symm_nsmul, map_sub, map_add, nsmulCoprimeAddAut_symm_smul] at h2
  rw [h2, factorSetAverage_apply, factorSetAverage_apply, factorSetAverage_apply]
  abel

end

section Coboundary

variable {A : Type*} [AddCommGroup A] {Q : Type*} [Group Q] [Finite Q] [DistribMulAction Q A]

theorem isCoboundary₂_of_isCocycle₂ (h : (Nat.card Q).Coprime (Nat.card A)) {c : Q × Q → A}
    (hc : groupCohomology.IsCocycle₂ c) : groupCohomology.IsCoboundary₂ c := by
  have : Fintype Q := Fintype.ofFinite Q
  refine ⟨factorSetAverage h (fun u v => c (u, v)), fun x y => ?_⟩
  have := factorSetAverage_coboundary h
    (c := fun u v => c (u, v)) (fun u v w => by simpa [add_comm] using hc u v w) x y
  rw [this]
  abel

end Coboundary

end CFSG.FeitThompson
