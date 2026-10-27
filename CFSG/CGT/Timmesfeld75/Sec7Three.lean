module

public import CFSG.CGT.Timmesfeld75.Sec7One
public import CFSG.CGT.Timmesfeld75.Sec66Stmt

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem nat_cases_of_not_two_odd {N : ℕ} (hN : 0 < N) (h4 : N ≠ 4) (hodd : ¬ Odd N)
    (h2 : ∀ k : ℕ, Odd k → N ≠ 2 * k) :
    (∃ i : ℕ, 1 ≤ i ∧ N = 8 * i) ∨ (∃ k : ℕ, Odd k ∧ 3 ≤ k ∧ N = 4 * k) := by
  obtain ⟨c, hc⟩ := Nat.not_odd_iff_even.1 hodd
  rcases Nat.even_or_odd c with hce | hco
  · obtain ⟨i, hi⟩ := hce
    rcases Nat.even_or_odd i with hie | hio
    · obtain ⟨j, hj⟩ := hie
      left
      exact ⟨j, by omega, by omega⟩
    · right
      refine ⟨i, hio, ?_, by omega⟩
      obtain ⟨a, ha⟩ := hio
      omega
  · exact absurd (by omega : N = 2 * c) (h2 c hco)

theorem Sec6Ctx.sec73 (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63) (h66 : Sec66)
    (hc : Sec6Ctx T T₁ n m) (hA8 : ¬ (n = 4 ∧ m = 1))
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m) {d e : G} (hd : d ∈ classD T)
    (he : e ∈ classD T) :
    (orderOf (d * e) = 4 ∨ Odd (orderOf (d * e)) ∨
        ∃ k : ℕ, Odd k ∧ orderOf (d * e) = 2 * k) ∧
      (orderOf (d * e) = 4 → (d * e) ^ 2 ∈ classD T) := by
  have := hc.finite
  refine ⟨?_, fun h4 => h66 G T T₁ n m hc d hd e he h4⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨h4, hodd, h2⟩ := hcon
  have hTab := hc.hy.pair.wc.1
  have hd2 : d * d = 1 := mul_self_eq_one_of_mem_classD hTab hd
  have he2 : e * e = 1 := mul_self_eq_one_of_mem_classD hTab he
  rcases nat_cases_of_not_two_odd (orderOf_pos (d * e)) h4 hodd h2 with ⟨i, hi, hNi⟩ |
    ⟨k, hk, hk3, hNk⟩
  ·
    have hy : ((d * e) ^ i)⁻¹ * d * (d * e) ^ i ∈ classD T := classD_conj hd ((d * e) ^ i)
    have hxy := dihedral_mul_conj_inv_pow hd2 he2 i
    have hord : orderOf (d * (((d * e) ^ i)⁻¹ * d * (d * e) ^ i)) = 4 := by
      rw [hxy, ← pow_add, orderOf_pow_of_dvd (by omega) (by rw [hNi]; exact ⟨4, by ring⟩), hNi]
      exact Nat.div_eq_of_eq_mul_left (by omega) (by ring)
    have hz := h66 G T T₁ n m hc d hd _ hy hord
    rw [hxy, ← pow_add, ← pow_mul] at hz
    exact hc.false_of_center_mem_D h1 h62 h63 hA8 hnat hd he (j := (i + i) * 2) (by omega)
      (by rw [hNi]; ring) hz
  ·
    obtain ⟨c, hc'⟩ := hk
    have hy : ((d * e) ^ c)⁻¹ * e * (d * e) ^ c ∈ classD T := classD_conj he ((d * e) ^ c)
    have hxy := dihedral_mul_conj_inv_pow' hd2 he2 c
    have hkc : 2 * c + 1 = k := by omega
    rw [hkc] at hxy
    have hord : orderOf (d * (((d * e) ^ c)⁻¹ * e * (d * e) ^ c)) = 4 := by
      rw [hxy, orderOf_pow_of_dvd (by omega) (by rw [hNk]; exact ⟨4, by ring⟩), hNk]
      exact Nat.div_eq_of_eq_mul_left (by omega) (by ring)
    have hz := h66 G T T₁ n m hc d hd _ hy hord
    rw [hxy, ← pow_mul] at hz
    exact hc.false_of_center_mem_D h1 h62 h63 hA8 hnat hd he (j := k * 2) (by omega)
      (by rw [hNk]; ring) hz

end CFSG.CGT.Timmesfeld75
