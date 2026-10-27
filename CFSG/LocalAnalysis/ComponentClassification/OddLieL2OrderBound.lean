module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpOddChar
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.LieArith

public section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.Blueprint (LieModel)

theorem sub_one_mul_sub_two_le_sq_sub_one (x : ℕ) : (x - 1) * (x - 2) ≤ x ^ 2 - 1 := by
  rcases Nat.lt_or_ge x 2 with h | h
  · interval_cases x <;> norm_num
  · obtain ⟨y, rfl⟩ : ∃ y, x = y + 2 := ⟨x - 2, by omega⟩
    have h1 : (y + 2 - 1) * (y + 2 - 2) = y * (y + 1) := by
      rw [show y + 2 - 1 = y + 1 by omega, show y + 2 - 2 = y by omega]
      exact Nat.mul_comm _ _
    have h2 : (y + 2) ^ 2 = y ^ 2 + 4 * y + 4 := by ring
    rw [h1, h2]
    have h3 : y ^ 2 + 4 * y + 4 - 1 = y ^ 2 + 4 * y + 3 := by omega
    rw [h3]
    nlinarith

theorem two_mul_lieOrderCofactor_lt_of_odd_ne_psl_two {t : StatedLieTag} {n r f : ℕ}
    (hadm : StatedLieAdmissible t n r f) (hr : r ≠ 2)
    (hA : ¬ (t = .PSL ∧ n = 2)) :
    2 * lieOrderCofactor t n (r ^ f) <
      (r ^ f) ^ (2 * lieSylowExponent t n) - 1 := by
  have hp : r.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hr3 : 3 ≤ r := by
    have h2 : 2 ≤ r := hp.two_le
    omega
  have ht : t ≠ .Tits := by
    intro ht
    subst ht
    have hr2 : r = 2 := hadm.2.2.2.1
    exact hr hr2
  have hX : ¬ (t = .PSL ∧ n = 3 ∧ r ^ f = 2) := by
    rintro ⟨-, -, h2⟩
    have hq3 : 3 ≤ r ^ f := by
      calc 3 ≤ r := hr3
        _ = r ^ 1 := (pow_one r).symm
        _ ≤ r ^ f := Nat.pow_le_pow_right (by omega) hf
    omega
  have hkey := CFSG.HardMathSupport.Dickson.Sec6.I923.cofactor_key hadm ht hA hX
  have hle := sub_one_mul_sub_two_le_sq_sub_one ((r ^ f) ^ lieSylowExponent t n)
  have hsq : ((r ^ f) ^ lieSylowExponent t n) ^ 2 =
      (r ^ f) ^ (2 * lieSylowExponent t n) := by
    rw [← pow_mul]
    ring_nf
  rw [hsq] at hle
  exact lt_of_lt_of_le hkey hle

theorem lieOrderNumerator_lt_of_odd_ne_psl_two {t : StatedLieTag} {n r f : ℕ}
    (hadm : StatedLieAdmissible t n r f) (hr : r ≠ 2)
    (hA : ¬ (t = .PSL ∧ n = 2)) :
    2 * lieOrderNumerator t n (r ^ f) <
      (r ^ f) ^ lieSylowExponent t n *
        (((r ^ f) ^ lieSylowExponent t n) ^ 2 - 1) := by
  have hC := two_mul_lieOrderCofactor_lt_of_odd_ne_psl_two hadm hr hA
  have hnum := lieOrderNumerator_eq hadm
  rw [hnum]
  have hpos : 0 < (r ^ f) ^ lieSylowExponent t n := by
    apply pow_pos
    have h3 : 3 ≤ r := by
      have h2 : 2 ≤ r := hadm.1.two_le
      omega
    positivity
  have hsq : ((r ^ f) ^ lieSylowExponent t n) ^ 2 =
      (r ^ f) ^ (2 * lieSylowExponent t n) := by
    rw [← pow_mul]
    ring_nf
  rw [hsq]
  calc 2 * ((r ^ f) ^ lieSylowExponent t n * lieOrderCofactor t n (r ^ f))
      = (r ^ f) ^ lieSylowExponent t n *
          (2 * lieOrderCofactor t n (r ^ f)) := by ring
    _ < (r ^ f) ^ lieSylowExponent t n *
          ((r ^ f) ^ (2 * lieSylowExponent t n) - 1) :=
        (Nat.mul_lt_mul_left hpos).mpr hC


theorem lieModel_odd_psl_two_unique {X : Type} [Group X]
    {t : StatedLieTag} {n r f r' f' : ℕ}
    (h : LieModel X t n r f) (h' : LieModel X .PSL 2 r' f')
    (hr : r ≠ 2) (hr' : r' ≠ 2) :
    t = .PSL ∧ n = 2 ∧ f = f' ∧ r = r' := by
  have hadm : StatedLieAdmissible t n r f := h.admissible
  have hadm' : StatedLieAdmissible .PSL 2 r' f' := h'.admissible
  have hrr : r = r' :=
    CFSG.ComponentClassification.GS82PumpInputs.oddLieCharUnique_holds X t n r f .PSL 2 r' f'
      hr hr' h h'
  obtain ⟨-, hmul, hfac⟩ := lieOrderFormulasInput X t n r f hadm h
  obtain ⟨-, hmul', hfac'⟩ := lieOrderFormulasInput X .PSL 2 r' f' hadm' h'
  have hN : lieSylowExponent .PSL 2 = 1 := by norm_num [lieSylowExponent]
  have hNf : lieSylowExponent t n * f = f' := by
    rw [hN, one_mul] at hfac'
    rw [← hrr] at hfac'
    rw [hfac] at hfac'
    exact hfac'
  have htn : t = .PSL ∧ n = 2 := by
    by_contra hA
    have hnum := lieOrderNumerator_eq hadm
    have hDpos : 0 < lieOrderDivisor t n (r ^ f) :=
      Nat.pos_of_ne_zero (lieOrderDivisor_ne_zero hadm)
    have hXle : Nat.card X ≤ (r ^ f) ^ lieSylowExponent t n *
        lieOrderCofactor t n (r ^ f) := by
      calc Nat.card X ≤ Nat.card X * lieOrderDivisor t n (r ^ f) :=
            Nat.le_mul_of_pos_right _ hDpos
        _ = lieOrderNumerator t n (r ^ f) := hmul
        _ = (r ^ f) ^ lieSylowExponent t n * lieOrderCofactor t n (r ^ f) := hnum
    have hNum := lieOrderNumerator_lt_of_odd_ne_psl_two hadm hr hA
    have hNum' : 2 * ((r ^ f) ^ lieSylowExponent t n *
          lieOrderCofactor t n (r ^ f)) <
        (r ^ f) ^ lieSylowExponent t n *
          (((r ^ f) ^ lieSylowExponent t n) ^ 2 - 1) := by
      rwa [hnum] at hNum
    have hXeq : 2 * Nat.card X =
        (r ^ f) ^ lieSylowExponent t n *
          (((r ^ f) ^ lieSylowExponent t n) ^ 2 - 1) := by
      have hodd : Odd (r' ^ f') := (hadm'.1.odd_of_ne_two hr').pow
      have hdiv : lieOrderDivisor .PSL 2 (r' ^ f') = 2 :=
        CFSG.ClassicalInvolution.gcd_two_sub_one_of_odd hodd
      have hnum' : lieOrderNumerator .PSL 2 (r' ^ f') =
          r' ^ f' * ((r' ^ f') ^ 2 - 1) := by
        simp [lieOrderNumerator]
      rw [hnum', hdiv] at hmul'
      have hQ' : r' ^ f' = (r ^ f) ^ lieSylowExponent t n := by
        calc r' ^ f' = r ^ (lieSylowExponent t n * f) := by rw [← hrr, ← hNf]
          _ = (r ^ lieSylowExponent t n) ^ f := by rw [pow_mul]
          _ = (r ^ f) ^ lieSylowExponent t n := by
              rw [← pow_mul, ← pow_mul]
              congr 1
              ring
      rw [hQ'] at hmul'
      rw [mul_comm (Nat.card X) 2] at hmul'
      exact hmul'
    have hle : 2 * Nat.card X ≤ 2 * ((r ^ f) ^ lieSylowExponent t n *
        lieOrderCofactor t n (r ^ f)) := Nat.mul_le_mul_left 2 hXle
    omega
  obtain ⟨rfl, rfl⟩ := htn
  exact ⟨rfl, rfl, by simpa [lieSylowExponent] using hNf, hrr⟩

end CFSG.ComponentClassification.CatLeafProof

end
