module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

@[expose] def HasFixedThreePair {G : Type*} [Group G] (α : MulAut G) : Prop :=
  ∃ x y : G, α x = x ∧ α y = y ∧ (orderOf x).Coprime 3 ∧ (orderOf y).Coprime 3 ∧
    orderOf (x * y) = 3

theorem HasFixedThreePair.of_conj {G : Type*} [Group G] {a : MulAut G} (c : MulAut G)
    (hc : HasFixedThreePair (c⁻¹ * a * c)) : HasFixedThreePair a := by
  obtain ⟨x, y, hx, hy, ox, oy, oxy⟩ := hc
  have hx' : a (c x) = c x := by
    have : c⁻¹ (a (c x)) = x := hx
    rw [← MulAut.apply_inv_self G c (a (c x)), this]
  have hy' : a (c y) = c y := by
    have : c⁻¹ (a (c y)) = y := hy
    rw [← MulAut.apply_inv_self G c (a (c y)), this]
  refine ⟨c x, c y, hx', hy', ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]; exact ox
  · rw [MulEquiv.orderOf_eq]; exact oy
  · rw [← map_mul, MulEquiv.orderOf_eq]; exact oxy

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem isPrimeFormGram_idGL : IsPrimeFormGram (1 : GL (Fin n) K) := by
  refine ⟨by rw [Units.val_one, transpose_one], fun i j => ?_⟩
  rw [Units.val_one, one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem fixed_conjHom_of_commute (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hcomm : (A : GL (Fin n) K) * (g : GL (Fin n) K) = (g : GL (Fin n) K) * (A : GL (Fin n) K)) :
    primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) A
      (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  rw [primeFormConjHom_mk]
  congr 1
  apply Subtype.ext
  change (A : GL (Fin n) K) * (g : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ = g
  rw [hcomm, mul_inv_cancel_right]

theorem fixed_fieldHom_of_map_eq (φ : K ≃+* K)
    (g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hg : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    primeFormFieldHom h (isPrimeFormGram_idGL (n := n)) φ
      (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  change primeFormFieldAut h (isPrimeFormGram_idGL (n := n)) φ _ = _
  rw [primeFormFieldAut_mk]
  congr 1
  apply Subtype.ext
  apply Units.ext
  exact hg

theorem orderOf_mk_dvd (g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (m : ℕ)
    (hg : (g : GL (Fin n) K) ^ m = 1) :
    orderOf (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ∣ m := by
  apply orderOf_dvd_of_pow_eq_one
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  have : g ^ m = 1 := Subtype.ext hg
  rw [this]
  exact one_mem _

theorem orderOf_mk_eq_three (g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hg : (g : GL (Fin n) K) ^ 3 = 1)
    (hns : ∀ s : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ s • 1) :
    orderOf (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 3 := by
  have h3 : (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, show g ^ 3 = 1 from Subtype.ext hg]
    rfl
  have hd := orderOf_dvd_of_pow_eq_one h3
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h1
  · exfalso
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
    obtain ⟨c, -, -, hc⟩ := h1
    apply hns (c : K)
    have := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hc
    simpa [GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply] using this
  · exact h1

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
