module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private lemma s11s_mem_closure_pair_inv {u w : G} (hu : u * u = 1) (hw : w * w = 1) {x : G}
    (hx : x ∈ Subgroup.closure ({u, w} : Set G)) :
    ∃ k : ℤ, x = (u * w) ^ k ∨ x = (u * w) ^ k * u := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_left hw
  have hconj : ∀ b : ℤ, u * (u * w) ^ b = (u * w) ^ (-b) * u := by
    intro b
    have h1 : u * (u * w) * u⁻¹ = (u * w)⁻¹ := by
      rw [huinv, mul_inv_rev, huinv, hwinv, ← mul_assoc, hu, one_mul]
    have h2 : u * (u * w) ^ b * u⁻¹ = (u * w) ^ (-b) := by
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h1, inv_zpow']
    calc u * (u * w) ^ b = u * (u * w) ^ b * u⁻¹ * u := by group
      _ = (u * w) ^ (-b) * u := by rw [h2]
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact ⟨0, Or.inr (by simp)⟩
    · refine ⟨-1, Or.inr ?_⟩
      rw [zpow_neg_one, mul_inv_rev, huinv, hwinv, mul_assoc, hu, mul_one]
  | one => exact ⟨0, Or.inl (by simp)⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, ha | ha⟩ := hy <;> obtain ⟨b, hb | hb⟩ := hz <;> subst ha <;> subst hb
    · exact ⟨a + b, Or.inl (zpow_add _ _ _).symm⟩
    · exact ⟨a + b, Or.inr (by rw [zpow_add, mul_assoc])⟩
    · refine ⟨a - b, Or.inr ?_⟩
      rw [mul_assoc, hconj, ← mul_assoc, ← zpow_add, sub_eq_add_neg]
    · refine ⟨a - b, Or.inl ?_⟩
      rw [mul_assoc, ← mul_assoc u, hconj, mul_assoc, hu, mul_one, ← zpow_add, sub_eq_add_neg]
  | inv y _ hy =>
    obtain ⟨a, ha | ha⟩ := hy <;> subst ha
    · exact ⟨-a, Or.inl (zpow_neg _ _).symm⟩
    · refine ⟨a, Or.inr ?_⟩
      rw [mul_inv_rev, huinv, ← zpow_neg, hconj, neg_neg]

private lemma s11s_conj_zpow_inv {s u : G} (hs : s * s = 1) (h : s * u * s = u⁻¹) (n : ℤ) :
    s * u ^ n * s = (u ^ n)⁻¹ := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs
  have h1 : MulAut.conj s u = u⁻¹ := by
    rw [MulAut.conj_apply, hsinv]
    exact h
  calc s * u ^ n * s = s * u ^ n * s⁻¹ := by rw [hsinv]
    _ = MulAut.conj s (u ^ n) := by rw [MulAut.conj_apply]
    _ = (MulAut.conj s u) ^ n := map_zpow _ _ _
    _ = (u⁻¹) ^ n := by rw [h1]
    _ = (u ^ n)⁻¹ := by rw [inv_zpow]

private lemma s11s_mul_pow_mul_self {s u : G} (hs : s * s = 1) (h : s * u * s = u⁻¹) (n : ℤ) :
    (u ^ n * s) * (u ^ n * s) = 1 := by
  have hc := s11s_conj_zpow_inv hs h n
  calc (u ^ n * s) * (u ^ n * s) = u ^ n * (s * u ^ n * s) := by group
    _ = u ^ n * (u ^ n)⁻¹ := by rw [hc]
    _ = 1 := by group

private lemma s11s_conj_conj {a b : G} (ha : a * a = 1) : a * (a * b * a⁻¹) * a⁻¹ = b := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
  calc a * (a * b * a⁻¹) * a⁻¹ = (a * a) * b * (a⁻¹ * a⁻¹) := by group
    _ = b := by rw [ha, one_mul, hainv, ha, mul_one]

theorem s11s_dihedral_trick {s k m e : G} (hs : s * s = 1) (hu : s * k⁻¹ * s * k = m * e)
    (hme : m * e = e * m) (he : e * e = 1) (hm : Odd (orderOf m)) :
    ∃ j : ℕ, (k * (s * k⁻¹ * s * k) ^ j)⁻¹ * s * (k * (s * k⁻¹ * s * k) ^ j) = s * e ∧
      s * e = e * s := by
  obtain ⟨j, hj⟩ := hm
  set u : G := s * k⁻¹ * s * k with hu_def
  have hsu : s * u = k⁻¹ * s * k := by
    rw [hu_def]
    simp only [← mul_assoc, hs, one_mul]
  have hA : s * u * s = u⁻¹ := by
    have h1 : s * u * s = k⁻¹ * s * k * s := by rw [hsu]
    rw [h1, hu_def]
    simp only [mul_inv_rev, inv_inv, inv_eq_of_mul_eq_one_left hs]
    group
  have hconj : ∀ n : ℤ, s * u ^ n * s = (u ^ n)⁻¹ := s11s_conj_zpow_inv hs hA
  have hconj_nat : ∀ n : ℕ, s * u ^ n * s = (u ^ n)⁻¹ := by
    intro n
    simpa only [zpow_natCast] using hconj (n : ℤ)
  have hjinv : (u ^ j)⁻¹ * s = s * u ^ j := by
    have h := hconj (j : ℤ)
    simp only [zpow_natCast] at h
    rw [← h]
    simp only [mul_assoc, hs, mul_one]
  have hme' : Commute m e := hme
  have he2 : e ^ 2 = 1 := by rw [pow_two]; exact he
  have he_pow : e ^ (2 * j + 1) = e := by
    rw [pow_succ, pow_mul, he2, one_pow, one_mul]
  have hm_pow : m ^ (2 * j + 1) = 1 := by
    rw [← hj, pow_orderOf_eq_one]
  have hu' : u = m * e := by rw [hu_def]; exact hu
  have huN : u ^ (2 * j + 1) = e := by
    rw [hu', hme'.mul_pow, hm_pow, he_pow, one_mul]
  refine ⟨j, ?_, ?_⟩
  · calc (k * u ^ j)⁻¹ * s * (k * u ^ j)
        = (u ^ j)⁻¹ * (k⁻¹ * s * k) * u ^ j := by group
      _ = (u ^ j)⁻¹ * (s * u) * u ^ j := by rw [hsu]
      _ = ((u ^ j)⁻¹ * s) * u * u ^ j := by group
      _ = (s * u ^ j) * u * u ^ j := by rw [hjinv]
      _ = s * u ^ (2 * j + 1) := by
            have h2 : (s * u ^ j) * u * u ^ j = s * (u ^ j * u * u ^ j) := by group
            rw [h2]
            congr 1
            rw [← pow_succ, ← pow_add]
            congr 1
            ring
      _ = s * e := by rw [huN]
  · have hses : s * e * s = e := by
      calc s * e * s = s * u ^ (2 * j + 1) * s := by rw [huN]
        _ = (u ^ (2 * j + 1))⁻¹ := hconj_nat (2 * j + 1)
        _ = e⁻¹ := by rw [huN]
        _ = e := inv_eq_of_mul_eq_one_left he
    calc s * e = s * e * s * s := by simp only [mul_assoc, hs, mul_one]
      _ = e * s := by rw [hses]

theorem s11s_mem_pair {t t' d : G} (ht : t * t = 1) (ht' : t' * t' = 1)
    (hd : d ∈ zpowers t ⊔ zpowers t') : ∃ k : ℤ, d = (t' * t) ^ k ∨ d = (t' * t) ^ k * t := by
  have hd' : d ∈ Subgroup.closure ({t', t} : Set G) := by
    have hset : ({t', t} : Set G) = ({t} ∪ {t'} : Set G) := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
      tauto
    rw [hset, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure t,
      ← Subgroup.zpowers_eq_closure t']
    exact hd
  obtain ⟨k, hk | hk⟩ := s11s_mem_closure_pair_inv ht' ht hd'
  · exact ⟨k, Or.inl hk⟩
  · refine ⟨k + 1, Or.inr ?_⟩
    rw [hk, zpow_add_one, mul_assoc]
    congr 1
    rw [mul_assoc, ht, mul_one]

theorem s11s_mem_zpowers_pair {t t' t'' w : G} (ht : t * t = 1) (ht' : t' * t' = 1)
    (ht'' : t'' * t'' = 1) (heq : zpowers t ⊔ zpowers t' = zpowers t ⊔ zpowers t'')
    (hw : w ∈ zpowers t ⊔ zpowers t') (hw2 : w * w ≠ 1) : t' * t ∈ zpowers (t'' * t) := by
  set y : G := t' * t with hy_def
  set y'' : G := t'' * t with hy''_def
  have hty : t * y * t = y⁻¹ := by
    rw [hy_def, mul_inv_rev, inv_eq_of_mul_eq_one_left ht',
      inv_eq_of_mul_eq_one_left ht]
    simp only [mul_assoc, ht, mul_one]
  have hty'' : t * y'' * t = y''⁻¹ := by
    rw [hy''_def, mul_inv_rev, inv_eq_of_mul_eq_one_left ht'',
      inv_eq_of_mul_eq_one_left ht]
    simp only [mul_assoc, ht, mul_one]
  have hyy : y * y ≠ 1 := by
    intro hy1
    obtain ⟨k, hk | hk⟩ := s11s_mem_pair ht ht' hw
    · apply hw2
      rw [hk, ← hy_def]
      have hy2 : y ^ (2 : ℤ) = 1 := by
        rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two]
        exact hy1
      rw [← zpow_add, show k + k = 2 * k by ring, zpow_mul, hy2, one_zpow]
    · apply hw2
      rw [hk, ← hy_def]
      exact s11s_mul_pow_mul_self ht hty k
  have hy_mem : y ∈ zpowers t ⊔ zpowers t' := by
    rw [hy_def]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers t'))
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  have hy_mem'' : y ∈ zpowers t ⊔ zpowers t'' := by
    rwa [heq] at hy_mem
  obtain ⟨k, hk | hk⟩ := s11s_mem_pair ht ht'' hy_mem''
  · rw [Subgroup.mem_zpowers_iff]
    rw [← hy''_def] at hk
    exact ⟨k, hk.symm⟩
  · exfalso
    apply hyy
    rw [hk, ← hy''_def]
    exact s11s_mul_pow_mul_self ht hty'' k

theorem s11s_exists_conj_sq {σ t : G} (hσ : σ * σ = 1) (ht : t * t = 1) (n : ℤ) :
    ∃ d ∈ zpowers t ⊔ zpowers (σ * t * σ⁻¹),
      σ * d⁻¹ * σ * d = (σ * t * σ⁻¹ * t) ^ n := by
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_left hσ
  set t' : G := σ * t * σ⁻¹ with ht'_def
  set y : G := t' * t with hy_def
  have hσtσ : σ * t * σ = t' := by rw [ht'_def, hσinv]
  have hσtσinv : σ * t * σ⁻¹ = t' := ht'_def.symm
  have ht' : t' * t' = 1 := by
    rw [ht'_def, ← MulAut.conj_apply, ← map_mul, ht, map_one]
  have hσt'σ : σ * t' * σ⁻¹ = t := by
    rw [ht'_def]
    exact s11s_conj_conj hσ
  have hy_mem : y ∈ zpowers t ⊔ zpowers t' := by
    rw [hy_def]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers t'))
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  have hσy : σ * y * σ⁻¹ = y⁻¹ := by
    calc σ * (t' * t) * σ⁻¹ = (σ * t' * σ⁻¹) * (σ * t * σ⁻¹) := by group
      _ = t * t' := by rw [hσt'σ, hσtσinv]
      _ = (t' * t)⁻¹ := by
            rw [mul_inv_rev, inv_eq_of_mul_eq_one_left ht',
              inv_eq_of_mul_eq_one_left ht]
  have hconj : ∀ m : ℤ, σ * y ^ m * σ⁻¹ = y ^ (-m) := by
    intro m
    have h2 : MulAut.conj σ y = y⁻¹ := by
      rw [MulAut.conj_apply]
      exact hσy
    calc σ * y ^ m * σ⁻¹ = MulAut.conj σ (y ^ m) := by rw [MulAut.conj_apply]
      _ = (MulAut.conj σ y) ^ m := map_zpow _ _ _
      _ = (y⁻¹) ^ m := by rw [h2]
      _ = y ^ (-m) := by rw [inv_zpow']
  have hσy' : ∀ m : ℤ, σ * y ^ m = y ^ (-m) * σ := by
    intro m
    rw [← hconj m, mul_assoc, inv_mul_cancel, mul_one]
  rcases Int.even_or_odd' n with ⟨k, hk | hk⟩
  · refine ⟨y ^ k, Subgroup.zpow_mem _ hy_mem k, ?_⟩
    rw [hk]
    have hσy_neg : σ * y ^ (-k) = y ^ k * σ := by
      have h := hσy' (-k)
      simpa only [neg_neg] using h
    calc σ * (y ^ k)⁻¹ * σ * y ^ k
        = σ * y ^ (-k) * σ * y ^ k := by rw [← zpow_neg]
      _ = (y ^ k * σ) * σ * y ^ k := by rw [hσy_neg]
      _ = y ^ k * y ^ k := by simp only [mul_assoc, hσ, mul_one, one_mul]
      _ = y ^ (2 * k) := by rw [← zpow_add, show k + k = 2 * k by ring]
  · refine ⟨t * y ^ k, Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
      (Subgroup.zpow_mem _ hy_mem k), ?_⟩
    rw [hk]
    have h1 : (t * y ^ k)⁻¹ = y ^ (-k) * t := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_left ht, ← zpow_neg]
    have hσy_neg : σ * y ^ (-k) = y ^ k * σ := by
      have h := hσy' (-k)
      simpa only [neg_neg] using h
    calc σ * (t * y ^ k)⁻¹ * σ * (t * y ^ k)
        = σ * (y ^ (-k) * t) * σ * (t * y ^ k) := by rw [h1]
      _ = σ * y ^ (-k) * t * σ * t * y ^ k := by group
      _ = (y ^ k * σ) * t * σ * t * y ^ k := by rw [hσy_neg]
      _ = y ^ k * (σ * t * σ) * t * y ^ k := by group
      _ = y ^ k * t' * t * y ^ k := by rw [hσtσ]
      _ = y ^ k * y * y ^ k := by
            have h3 : y ^ k * t' * t * y ^ k = y ^ k * (t' * t) * y ^ k := by group
            rw [h3, ← hy_def]
      _ = y ^ (2 * k + 1) := by
            rw [← zpow_add_one, ← zpow_add]
            congr 1
            ring

theorem s11s_mem_zpowers_of_odd {y : G} {n : ℕ} (hy : y ^ 2 ^ n = 1) {k : ℤ} (hk : Odd k) :
    y ∈ zpowers (y ^ k) := by
  have hdvd : orderOf y ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hy
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hcop : Nat.Coprime k.natAbs (orderOf y) := by
    rw [hi]
    exact Nat.Coprime.pow_right i (hk.natAbs.coprime_two_right)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hmem : y ^ k.natAbs ∈ zpowers (y ^ k) := by
    rcases Int.natAbs_eq k with h | h
    · rw [← zpow_natCast y k.natAbs, ← h]
      exact Subgroup.mem_zpowers (y ^ k)
    · have hk' : (k.natAbs : ℤ) = -k := by
        have h' : -k = -(-(k.natAbs : ℤ)) := congrArg Neg.neg h
        simpa only [neg_neg] using h'.symm
      rw [← zpow_natCast y k.natAbs, hk', zpow_neg]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers (y ^ k))
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨j * m, ?_⟩
  calc (y ^ k) ^ (j * m) = ((y ^ k) ^ j) ^ (m : ℤ) := zpow_mul _ _ _
    _ = ((y ^ k) ^ j) ^ m := by rw [zpow_natCast]
    _ = (y ^ k.natAbs) ^ m := by rw [hj]
    _ = y := hm

end CFSG.OddStandard.SmallF3.Omega
