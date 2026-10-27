module

public import CFSG.GH74.GLS.IVK.Lifted.Lem119V
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.IVK.Lifted CFSG.LocalAnalysis.ComponentInitial

theorem field_part_pow_two {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h3 : 3 < Nat.card F) (α : MulAut (Matrix.SpecialLinearGroup (Fin 2) F)) {m : ℕ}
    (hm : α ^ (2 ^ m) = 1) : ((gammaOf hodd h3 α).right) ^ (2 ^ m) = 1 := by
  have h1 : (gammaOf hodd h3 α) ^ (2 ^ m) = 1 := by rw [← map_pow, hm, map_one]
  have h2 := congrArg (SemidirectProduct.rightHom : _ →* (F ≃+* F)) h1
  rw [map_pow, map_one] at h2
  exact h2

theorem field_part_trivial_big {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h3 : 3 < Nat.card F) {n : ℕ} (hn : 2 ≤ n)
    (hv : (Nat.card ↥(StatedSL 2 F)).factorization 2 = n + 1)
    {c : Matrix.SpecialLinearGroup (Fin 2) F} (hc : orderOf c = 2 ^ n)
    (α : MulAut (Matrix.SpecialLinearGroup (Fin 2) F)) (hαc : α c = c)
    (h2pow : ∃ m : ℕ, α ^ (2 ^ m) = 1) : (gammaOf hodd h3 α).right = 1 := by
  have _hn : 2 ≤ n := hn
  by_contra hσ
  obtain ⟨m, hm⟩ := h2pow
  have hσm := field_part_pow_two hodd h3 α hm
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hσm)
  have hcard : Nat.card ↥(StatedSL 2 F) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv).symm
  have hcongr : MulAut.congr (MulEquiv.refl (Matrix.SpecialLinearGroup (Fin 2) F)) α = α := by
    ext x; rfl
  refine not_fixes_big_cyclic hodd h3 (MulEquiv.refl _) α ?_ ⟨j, ?_⟩ (b := c) ?_ hc ?_
  · rw [hcongr]; exact hσ
  · rw [hcongr]; exact hj
  · exact hαc
  · rw [← hcard, hv]

theorem field_part_trivial_small {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h3 : 3 < Nat.card F) (hmod : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5)
    (α : MulAut (Matrix.SpecialLinearGroup (Fin 2) F)) (h2pow : ∃ m : ℕ, α ^ (2 ^ m) = 1) :
    (gammaOf hodd h3 α).right = 1 := by
  obtain ⟨m, hm⟩ := h2pow
  have hσm := field_part_pow_two hodd h3 α hm
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨e, hp, hcard⟩ := FiniteField.card F (ringChar F)
  have hK : Nat.card F = ringChar F ^ (e : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨hcardAut, -⟩ := card_ringAut_and_isCyclic hp F hK
  have heodd : Odd (e : ℕ) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨k, hk⟩ := hev
    have hpodd : Odd (ringChar F) := by
      by_contra hne
      have hev2 : Even (ringChar F) := Nat.not_odd_iff_even.1 hne
      have : Even (Nat.card F) := by
        rw [hK]; exact Nat.even_pow.2 ⟨hev2, e.ne_zero⟩
      exact (Nat.not_even_iff_odd.2 hodd) this
    have hsq : Nat.card F = (ringChar F ^ k) ^ 2 := by rw [hK, hk, ← two_mul, pow_mul']
    have hoddk : Odd (ringChar F ^ k) := hpodd.pow
    obtain ⟨t, ht⟩ := hoddk
    have : Nat.card F % 8 = 1 := by
      rw [hsq, ht]
      have : (2 * t + 1) ^ 2 = 4 * (t * (t + 1)) + 1 := by ring
      rw [this]
      have h2 : 2 ∣ t * (t + 1) := (Nat.even_mul_succ_self t).two_dvd
      obtain ⟨s, hs⟩ := h2
      rw [hs]; omega
    omega
  have hdvd1 : orderOf (gammaOf hodd h3 α).right ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hσm
  have hdvd2 : orderOf (gammaOf hodd h3 α).right ∣ (e : ℕ) := by
    rw [← hcardAut]; exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ m) (e : ℕ) := Nat.Coprime.pow_left m (Nat.coprime_two_left.2 heodd)
  have : orderOf (gammaOf hodd h3 α).right = 1 :=
    Nat.Coprime.eq_one_of_dvd ((hcop.coprime_dvd_left hdvd1).coprime_dvd_right hdvd2).symm (dvd_refl _)
  exact orderOf_eq_one_iff.1 this

end CFSG.GH74.GLS.Stage1.Main
