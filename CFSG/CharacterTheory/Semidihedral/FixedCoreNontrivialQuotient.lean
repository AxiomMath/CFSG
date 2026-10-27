module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialLocal

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

variable {E : Type*} [Group E]

theorem exists_mem_centralizer_of_commutator_mem [Finite E] {O P : Subgroup E}
    (hOn : ∀ g : E, ∀ o ∈ O, g * o * g⁻¹ ∈ O) (hO : Odd (Nat.card O)) (hP : IsPGroup 2 P)
    {x : E} (hx : ∀ p ∈ P, x⁻¹ * p * x * p⁻¹ ∈ O) :
    ∃ o ∈ O, x * o ∈ Subgroup.centralizer (P : Set E) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let act : MulAction P O :=
    { smul := fun p o => ⟨x⁻¹ * (p : E) * x * (o : E) * (p : E)⁻¹, by
        have h1 := hx p p.2
        have h2 := hOn p o o.2
        have : x⁻¹ * (p : E) * x * (o : E) * (p : E)⁻¹ =
            (x⁻¹ * p * x * (p : E)⁻¹) * (p * o * (p : E)⁻¹) := by group
        rw [this]
        exact O.mul_mem h1 h2⟩
      one_smul := fun o => by
        apply Subtype.ext
        change x⁻¹ * ((1 : P) : E) * x * (o : E) * ((1 : P) : E)⁻¹ = o
        simp
      mul_smul := fun p q o => by
        apply Subtype.ext
        change x⁻¹ * ((p * q : P) : E) * x * (o : E) * ((p * q : P) : E)⁻¹ =
          x⁻¹ * (p : E) * x * (x⁻¹ * (q : E) * x * (o : E) * (q : E)⁻¹) * (p : E)⁻¹
        simp only [Subgroup.coe_mul]
        group }
  have hnd : ¬ 2 ∣ Nat.card O := fun h => (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr h)
  obtain ⟨o, ho⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card O hnd
  refine ⟨o, o.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  have hfix := congrArg Subtype.val (ho ⟨p, hp⟩)
  change x⁻¹ * p * x * (o : E) * (p : E)⁻¹ = o at hfix
  calc p * (x * o) = x * (x⁻¹ * p * x * (o : E) * p⁻¹) * p := by group
    _ = x * o * p := by rw [hfix]

theorem mem_of_pow_two_pow_eq_one [Finite E] {A : Subgroup E} [A.Normal] (hA : Odd A.index)
    {x : E} {k : ℕ} (hx : x ^ 2 ^ k = 1) : x ∈ A := by
  have h1 : (QuotientGroup.mk x : E ⧸ A) ^ 2 ^ k = 1 := by
    rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one]
  have hdvd1 := orderOf_dvd_of_pow_eq_one h1
  have hdvd2 : orderOf (QuotientGroup.mk x : E ⧸ A) ∣ A.index := by
    rw [Subgroup.index]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (orderOf (QuotientGroup.mk x : E ⧸ A)) (2 ^ k) := by
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr (hA.of_dvd_nat hdvd2))
  have h := Nat.Coprime.eq_one_of_dvd hcop hdvd1
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h
  exact h

theorem mem_of_conj_eq_inv [Finite E] {A : Subgroup E} [A.Normal] (hA : Odd A.index)
    {a y : E} (ha : a ∈ A) (hy : a * y * a⁻¹ = y⁻¹) : y ∈ A := by
  have hmk : (QuotientGroup.mk a : E ⧸ A) = 1 := (QuotientGroup.eq_one_iff a).mpr ha
  have h1 : (QuotientGroup.mk y : E ⧸ A) = (QuotientGroup.mk y)⁻¹ := by
    have := congrArg (QuotientGroup.mk : E → E ⧸ A) hy
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      hmk, one_mul, inv_one, mul_one] at this
    exact this
  have h2 : (QuotientGroup.mk y : E ⧸ A) ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [h1]
    exact inv_mul_cancel _
  have hdvd1 := orderOf_dvd_of_pow_eq_one h2
  have hdvd2 : orderOf (QuotientGroup.mk y : E ⧸ A) ∣ A.index := by
    rw [Subgroup.index]
    exact orderOf_dvd_natCard _
  have hodd := hA.of_dvd_nat hdvd2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd1 with h | h
  · rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h
    exact h
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem mem_dihedral_cases {d s : E} (hs : s * s = 1) (hsd : s * d * s⁻¹ = d⁻¹) {x : E}
    (hx : x ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers s) :
    ∃ i : ℤ, x = d ^ i ∨ x = d ^ i * s := by
  have hsi : s⁻¹ = s := (eq_inv_of_mul_eq_one_left hs).symm
  have hsdi : ∀ i : ℤ, s * d ^ i * s⁻¹ = d ^ (-i) := by
    intro i
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hsd, inv_zpow', zpow_neg]
  have hds : ∀ i : ℤ, s * d ^ i = d ^ (-i) * s := by
    intro i
    calc s * d ^ i = s * d ^ i * s⁻¹ * s := by group
      _ = d ^ (-i) * s := by rw [hsdi]
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ⟨i, Or.inl rfl⟩
    · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rcases zpowers_cases_of_mul_self hs (s ^ j) (Subgroup.zpow_mem_zpowers s j) with h | h
      · exact ⟨0, Or.inl (by rw [h, zpow_zero])⟩
      · exact ⟨0, Or.inr (by rw [h, zpow_zero, one_mul])⟩
  | one => exact ⟨0, Or.inl (zpow_zero d).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, hi | hi⟩ := hx <;> obtain ⟨j, hj | hj⟩ := hy <;> subst hi hj
    · exact ⟨i + j, Or.inl (zpow_add d i j).symm⟩
    · exact ⟨i + j, Or.inr (by rw [zpow_add]; group)⟩
    · refine ⟨i - j, Or.inr ?_⟩
      calc d ^ i * s * d ^ j = d ^ i * (s * d ^ j) := by group
        _ = d ^ i * (d ^ (-j) * s) := by rw [hds]
        _ = d ^ (i - j) * s := by rw [sub_eq_add_neg, zpow_add]; group
    · refine ⟨i - j, Or.inl ?_⟩
      calc d ^ i * s * (d ^ j * s) = d ^ i * (s * d ^ j) * s := by group
        _ = d ^ i * (d ^ (-j) * s) * s := by rw [hds]
        _ = d ^ (i - j) * (s * s) := by rw [sub_eq_add_neg, zpow_add]; group
        _ = d ^ (i - j) := by rw [hs, mul_one]
  | inv x _ hx =>
    obtain ⟨i, hi | hi⟩ := hx <;> subst hi
    · exact ⟨-i, Or.inl (zpow_neg d i).symm⟩
    · refine ⟨i, Or.inr ?_⟩
      calc (d ^ i * s)⁻¹ = s⁻¹ * d ^ (-i) := by rw [mul_inv_rev, zpow_neg]
        _ = s * d ^ (-i) := by rw [hsi]
        _ = d ^ (- -i) * s := hds (-i)
        _ = d ^ i * s := by rw [neg_neg]

theorem zpow_mul_sq {d s : E} (hs : s * s = 1) (hsd : s * d * s⁻¹ = d⁻¹) (i : ℤ) :
    d ^ i * s * (d ^ i * s) = 1 := by
  have hsdi : s * d ^ i * s⁻¹ = d ^ (-i) := by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hsd, inv_zpow', zpow_neg]
  have hsi : s⁻¹ = s := (eq_inv_of_mul_eq_one_left hs).symm
  calc d ^ i * s * (d ^ i * s) = d ^ i * (s * d ^ i * s⁻¹) * (s * s) := by group
    _ = 1 := by rw [hsdi, hs, mul_one, ← zpow_add, add_neg_cancel, zpow_zero]

theorem commute_of_odd_of_normalizes [Finite E] {d s x : E} (hd4 : orderOf d = 4)
    (hs : s * s = 1) (hsd : s * d * s⁻¹ = d⁻¹) (hsnot : s ∉ Subgroup.zpowers d)
    (hxodd : Odd (orderOf x))
    (hxN : x ∈ Subgroup.normalizer
      ((Subgroup.zpowers d ⊔ Subgroup.zpowers s : Subgroup E) : Set E)) :
    x * d = d * x ∧ x * s = s * x := by
  set D8 : Subgroup E := Subgroup.zpowers d ⊔ Subgroup.zpowers s
  have hconjD : ∀ y ∈ D8, x * y * x⁻¹ ∈ D8 := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp hxN y).mp hy
  have hdD : d ∈ D8 := Subgroup.mem_sup_left (Subgroup.mem_zpowers d)
  have hsD : s ∈ D8 := Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
  have hxd : x * d = d * x := by
    obtain ⟨i, hi | hi⟩ := mem_dihedral_cases hs hsd (hconjD d hdD)
    · have ho : orderOf (d ^ i) = 4 := by
        rw [← hi, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hd4]
      have hiodd : Odd i := by
        rcases Int.even_or_odd i with ⟨j, rfl⟩ | h
        · exfalso
          have h2 : (d ^ (j + j)) ^ 2 = 1 := by
            rw [← zpow_natCast, ← zpow_mul, show (j + j) * ((2 : ℕ) : ℤ) = 4 * j by push_cast; ring,
              zpow_mul, show ((4 : ℤ)) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast,
              ← hd4, pow_orderOf_eq_one, one_zpow]
          have := orderOf_dvd_of_pow_eq_one h2
          rw [ho] at this
          norm_num at this
        · exact h
      have hsq : (x * x) * d * (x * x)⁻¹ = d := by
        have h1 : x * d * x⁻¹ = d ^ i := hi
        have h2 : (x * x) * d * (x * x)⁻¹ = x * (d ^ i) * x⁻¹ := by
          rw [← h1]; group
        rw [h2, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h1, ← zpow_mul]
        obtain ⟨k, rfl⟩ := hiodd
        have : (2 * k + 1) * (2 * k + 1) = 4 * (k * k + k) + 1 := by ring
        rw [this, zpow_add, zpow_mul, show ((4 : ℤ)) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast,
          ← hd4, pow_orderOf_eq_one, one_zpow, one_mul, zpow_one]
      have hxx : x ∈ Subgroup.zpowers (x * x) := mem_zpowers_sq_of_odd hxodd
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxx
      have hc : Commute (x * x) d := by
        calc (x * x) * d = (x * x) * d * (x * x)⁻¹ * (x * x) := by group
          _ = d * (x * x) := by rw [hsq]
      rw [← hk]
      exact (hc.zpow_left k)
    · exfalso
      have h2 := zpow_mul_sq hs hsd i
      have ho : orderOf (d ^ i * s) = 4 := by
        rw [← hi, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hd4]
      have := orderOf_dvd_of_pow_eq_one (show (d ^ i * s) ^ 2 = 1 by rw [pow_two]; exact h2)
      rw [ho] at this
      norm_num at this
  refine ⟨hxd, ?_⟩
  have hxdz : ∀ j : ℤ, x * d ^ j = d ^ j * x := fun j => (Commute.zpow_right hxd j)
  obtain ⟨j, hj | hj⟩ := mem_dihedral_cases hs hsd (hconjD s hsD)
  · exfalso
    apply hsnot
    have : s = d ^ j := by
      calc s = x⁻¹ * (x * s * x⁻¹) * x := by group
        _ = x⁻¹ * d ^ j * x := by rw [hj]
        _ = d ^ j := by
          calc x⁻¹ * d ^ j * x = x⁻¹ * (d ^ j * x) := by group
            _ = x⁻¹ * (x * d ^ j) := by rw [hxdz]
            _ = d ^ j := by group
    rw [this]
    exact Subgroup.zpow_mem_zpowers d j
  · have hpow : ∀ n : ℕ, x ^ n * s * (x ^ n)⁻¹ = d ^ ((n : ℤ) * j) * s := by
      intro n
      induction n with
      | zero => simp
      | succ m ih =>
        calc x ^ (m + 1) * s * (x ^ (m + 1))⁻¹ = x * (x ^ m * s * (x ^ m)⁻¹) * x⁻¹ := by
              rw [pow_succ']; group
          _ = x * (d ^ ((m : ℤ) * j) * s) * x⁻¹ := by rw [ih]
          _ = d ^ ((m : ℤ) * j) * (x * s * x⁻¹) := by
              calc x * (d ^ ((m : ℤ) * j) * s) * x⁻¹ = (x * d ^ ((m : ℤ) * j)) * s * x⁻¹ := by
                    group
                _ = (d ^ ((m : ℤ) * j) * x) * s * x⁻¹ := by rw [hxdz]
                _ = d ^ ((m : ℤ) * j) * (x * s * x⁻¹) := by group
          _ = d ^ (((m + 1 : ℕ) : ℤ) * j) * s := by
              rw [hj, ← mul_assoc, ← zpow_add]; push_cast; ring_nf
    have hk := hpow (orderOf x)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hk
    have hdj : d ^ ((orderOf x : ℤ) * j) = 1 := by
      calc d ^ ((orderOf x : ℤ) * j) = d ^ ((orderOf x : ℤ) * j) * s * s⁻¹ := by group
        _ = 1 := by rw [← hk, mul_inv_cancel]
    rw [← orderOf_dvd_iff_zpow_eq_one, hd4] at hdj
    have h4j : (4 : ℤ) ∣ j := by
      have hcop : Nat.Coprime 4 (orderOf x) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hxodd)
      refine Int.dvd_of_dvd_mul_right_of_gcd_one (b := (orderOf x : ℤ)) (by exact_mod_cast hdj) ?_
      have h := Int.gcd_natCast_natCast 4 (orderOf x)
      rw [hcop] at h
      exact_mod_cast h
    obtain ⟨m, rfl⟩ := h4j
    have hd1 : d ^ (4 * m) = 1 := by
      rw [zpow_mul, show ((4 : ℤ)) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast, ← hd4,
        pow_orderOf_eq_one, one_zpow]
    rw [hd1, one_mul] at hj
    calc x * s = x * s * x⁻¹ * x := by group
      _ = s * x := by rw [hj]

end CFSG.Semidihedral.FixedCoreNontrivial
