module

public import CFSG.CharacterTheory.Wreathed.ConditionalGlobalDegreesRows
public import CFSG.CharacterTheory.Wreathed.ConditionalSquareRootAlgebra

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.ConditionalExactOrder

open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalGeneralBase
  CFSG.Wreathed.ConditionalCompleteBase CFSG.Wreathed.ConditionalFiveFixed
  CFSG.Wreathed.ConditionalGlobalDegrees

variable {ι : Type*} [DecidableEq ι]

structure BlockFamilies (p A Bq Dq ω : ι) (M : ℕ) (J : Finset ℕ) (χ : ℕ → ι)
    (γ : ℕ → Fin 4 → ι) (P Q : ℕ → Fin 2 → ι) {m : ℕ} (ψ : ZMod m × ZMod m → ι)
    (V : Finset (ZMod m × ZMod m)) : Prop where
  hAp : A ≠ p
  hBp : Bq ≠ p
  hDp : Dq ≠ p
  hωp : ω ≠ p
  hBA : Bq ≠ A
  hDA : Dq ≠ A
  hωA : ω ≠ A
  hDB : Dq ≠ Bq
  hωB : ω ≠ Bq
  hωD : ω ≠ Dq
  hχcore : ∀ j ∈ J, χ j ≠ p ∧ χ j ≠ A ∧ χ j ≠ Bq ∧ χ j ≠ Dq ∧ χ j ≠ ω
  hχinj : Set.InjOn χ J
  γinj : ∀ r ∈ Finset.Ico 1 M, Function.Injective (γ r)
  γcore : ∀ r ∈ Finset.Ico 1 M, ∀ l,
    γ r l ≠ p ∧ γ r l ≠ A ∧ γ r l ≠ Bq ∧ γ r l ≠ Dq ∧ γ r l ≠ ω
  γodd : ∀ r ∈ Finset.Ico 1 M, ∀ l, ∀ j ∈ J, γ r l ≠ χ j
  disj : ∀ r ∈ Finset.Ico 1 M, ∀ t ∈ Finset.Ico 1 M, r ≠ t → ∀ l l', γ r l ≠ γ t l'
  lab : ∀ r ∈ Finset.Ico 1 M,
    ({P r 0, Q r 0, P r 1, Q r 1} : Finset ι) = Finset.univ.image (γ r)
  gen : ∀ I ∈ V, ψ I ≠ p ∧ ψ I ≠ A ∧ ψ I ≠ Bq ∧ ψ I ≠ Dq ∧ ψ I ≠ ω ∧
    (∀ j ∈ J, ψ I ≠ χ j) ∧ ∀ r ∈ Finset.Ico 1 M, ∀ l, ψ I ≠ γ r l
  geninj : Set.InjOn ψ V

namespace BlockFamilies

variable {p A Bq Dq ω : ι} {M : ℕ} {J : Finset ℕ} {χ : ℕ → ι} {γ : ℕ → Fin 4 → ι}
  {P Q : ℕ → Fin 2 → ι} {m : ℕ} {ψ : ZMod m × ZMod m → ι} {V : Finset (ZMod m × ZMod m)}
  (T : BlockFamilies p A Bq Dq ω M J χ γ P Q ψ V)
include T

theorem P_eq {r : ℕ} (hr : r ∈ Finset.Ico 1 M) (e : Fin 2) : ∃ l, P r e = γ r l :=
  ((labels_of_image (T.γinj r hr) (T.lab r hr)).1 e).1

theorem Q_eq {r : ℕ} (hr : r ∈ Finset.Ico 1 M) (e : Fin 2) : ∃ l, Q r e = γ r l :=
  ((labels_of_image (T.γinj r hr) (T.lab r hr)).1 e).2

theorem P_inj {r t : ℕ} (hr : r ∈ Finset.Ico 1 M) (ht : t ∈ Finset.Ico 1 M) {e e' : Fin 2}
    (h : P r e = P t e') : r = t ∧ e = e' := by
  by_cases hrt : r = t
  · subst hrt
    exact ⟨rfl, (labels_of_image (T.γinj r hr) (T.lab r hr)).2.1 h⟩
  · obtain ⟨l, hl⟩ := T.P_eq hr e
    obtain ⟨l', hl'⟩ := T.P_eq ht e'
    exact absurd (hl.symm.trans (h.trans hl')) (T.disj r hr t ht hrt l l')

theorem Q_inj {r t : ℕ} (hr : r ∈ Finset.Ico 1 M) (ht : t ∈ Finset.Ico 1 M) {e e' : Fin 2}
    (h : Q r e = Q t e') : r = t ∧ e = e' := by
  by_cases hrt : r = t
  · subst hrt
    exact ⟨rfl, (labels_of_image (T.γinj r hr) (T.lab r hr)).2.2.1 h⟩
  · obtain ⟨l, hl⟩ := T.Q_eq hr e
    obtain ⟨l', hl'⟩ := T.Q_eq ht e'
    exact absurd (hl.symm.trans (h.trans hl')) (T.disj r hr t ht hrt l l')

theorem P_ne_Q {r t : ℕ} (hr : r ∈ Finset.Ico 1 M) (ht : t ∈ Finset.Ico 1 M) (e e' : Fin 2) :
    P r e ≠ Q t e' := by
  intro h
  by_cases hrt : r = t
  · subst hrt
    exact (labels_of_image (T.γinj r hr) (T.lab r hr)).2.2.2 e e' h
  · obtain ⟨l, hl⟩ := T.P_eq hr e
    obtain ⟨l', hl'⟩ := T.Q_eq ht e'
    exact T.disj r hr t ht hrt l l' (hl.symm.trans (h.trans hl'))

theorem label_out {r : ℕ} (hr : r ∈ Finset.Ico 1 M) {φ : ι} (hφ : ∃ l, φ = γ r l) :
    φ ≠ p ∧ φ ≠ A ∧ φ ≠ Bq ∧ φ ≠ Dq ∧ φ ≠ ω ∧ (∀ j ∈ J, φ ≠ χ j) ∧ ∀ I ∈ V, φ ≠ ψ I := by
  obtain ⟨l, rfl⟩ := hφ
  obtain ⟨n1, n2, n3, n4, n5⟩ := T.γcore r hr l
  exact ⟨n1, n2, n3, n4, n5, fun j hj => T.γodd r hr l j hj,
    fun I hI h => (T.gen I hI).2.2.2.2.2.2 r hr l h.symm⟩

theorem sum_union {B : Finset ι}
    (hB : B = ({p, A, Bq, Dq, ω} : Finset ι) ∪ J.image χ ∪
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun re => P re.1 re.2) ∪
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun re => Q re.1 re.2) ∪
      V.image ψ) (F : ι → ℂ) :
    ∑ φ ∈ B, F φ = F p + F A + F Bq + F Dq + F ω + ∑ j ∈ J, F (χ j) +
      ∑ re ∈ Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2)), F (P re.1 re.2) +
      ∑ re ∈ Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2)), F (Q re.1 re.2) +
      ∑ I ∈ V, F (ψ I) := by
  have h1 : Disjoint ({p, A, Bq, Dq, ω} : Finset ι) (J.image χ) := by
    rw [Finset.disjoint_right]
    intro φ hφ
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hφ
    obtain ⟨n1, n2, n3, n4, n5⟩ := T.hχcore j hj
    simp [n1, n2, n3, n4, n5]
  have h2 : Disjoint (({p, A, Bq, Dq, ω} : Finset ι) ∪ J.image χ)
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun re => P re.1 re.2) := by
    rw [Finset.disjoint_right]
    intro φ hφ
    obtain ⟨⟨r, e⟩, hre, rfl⟩ := Finset.mem_image.mp hφ
    have hr := (Finset.mem_product.mp hre).1
    obtain ⟨n1, n2, n3, n4, n5, n6, -⟩ := T.label_out hr (T.P_eq hr e)
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      not_or]
    exact ⟨⟨n1, n2, n3, n4, n5⟩, fun ⟨j, hj, h⟩ => n6 j hj h.symm⟩
  have h3 : Disjoint (({p, A, Bq, Dq, ω} : Finset ι) ∪ J.image χ ∪
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun re => P re.1 re.2))
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun re => Q re.1 re.2) := by
    rw [Finset.disjoint_right]
    intro φ hφ
    obtain ⟨⟨r, e⟩, hre, rfl⟩ := Finset.mem_image.mp hφ
    have hr := (Finset.mem_product.mp hre).1
    obtain ⟨n1, n2, n3, n4, n5, n6, -⟩ := T.label_out hr (T.Q_eq hr e)
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      not_or]
    refine ⟨⟨⟨n1, n2, n3, n4, n5⟩, fun ⟨j, hj, h⟩ => n6 j hj h.symm⟩, ?_⟩
    rintro ⟨⟨r', e'⟩, hre', h⟩
    exact T.P_ne_Q (Finset.mem_product.mp hre').1 hr e' e h
  have h4 : Disjoint (({p, A, Bq, Dq, ω} : Finset ι) ∪ J.image χ ∪
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun re => P re.1 re.2) ∪
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun re => Q re.1 re.2))
      (V.image ψ) := by
    rw [Finset.disjoint_right]
    intro φ hφ
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hφ
    obtain ⟨n1, n2, n3, n4, n5, n6, -⟩ := T.gen I hI
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      not_or]
    refine ⟨⟨⟨⟨n1, n2, n3, n4, n5⟩, fun ⟨j, hj, h⟩ => n6 j hj h.symm⟩, ?_⟩, ?_⟩
    · rintro ⟨⟨r', e'⟩, hre', h⟩
      have hr' := (Finset.mem_product.mp hre').1
      exact (T.label_out hr' (T.P_eq hr' e')).2.2.2.2.2.2 I hI h
    · rintro ⟨⟨r', e'⟩, hre', h⟩
      have hr' := (Finset.mem_product.mp hre').1
      exact (T.label_out hr' (T.Q_eq hr' e')).2.2.2.2.2.2 I hI h
  have iP : Set.InjOn (fun re : ℕ × Fin 2 => P re.1 re.2)
      (Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2)) : Finset (ℕ × Fin 2)) := by
    rintro ⟨r, e⟩ hre ⟨r', e'⟩ hre' h
    obtain ⟨h₁, h₂⟩ := T.P_inj (Finset.mem_product.mp hre).1 (Finset.mem_product.mp hre').1 h
    exact Prod.ext h₁ h₂
  have iQ : Set.InjOn (fun re : ℕ × Fin 2 => Q re.1 re.2)
      (Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2)) : Finset (ℕ × Fin 2)) := by
    rintro ⟨r, e⟩ hre ⟨r', e'⟩ hre' h
    obtain ⟨h₁, h₂⟩ := T.Q_inj (Finset.mem_product.mp hre).1 (Finset.mem_product.mp hre').1 h
    exact Prod.ext h₁ h₂
  have hcore : ∑ φ ∈ ({p, A, Bq, Dq, ω} : Finset ι), F φ = F p + F A + F Bq + F Dq + F ω := by
    rw [Finset.sum_insert (by simp [T.hAp.symm, T.hBp.symm, T.hDp.symm, T.hωp.symm]),
      Finset.sum_insert (by simp [T.hBA.symm, T.hDA.symm, T.hωA.symm]),
      Finset.sum_insert (by simp [T.hDB.symm, T.hωB.symm]),
      Finset.sum_insert (by simp [T.hωD.symm]), Finset.sum_singleton]
    ring
  rw [hB, Finset.sum_union h4, Finset.sum_union h3, Finset.sum_union h2, Finset.sum_union h1,
    hcore, Finset.sum_image T.hχinj, Finset.sum_image iP, Finset.sum_image iQ,
    Finset.sum_image T.geninj]

end BlockFamilies

theorem sum_labels_parity {K : ℕ} (hK : 1 ≤ K) (g : ℕ × Fin 2 → ℂ) (a b : ℂ)
    (hg : ∀ r e, g (r, e) = if Odd r then a else b) :
    ∑ re ∈ Finset.Ico 1 (2 * K) ×ˢ (Finset.univ : Finset (Fin 2)), g re =
      2 * (K * a + ((K : ℂ) - 1) * b) := by
  rw [Finset.sum_product]
  simp only [hg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
    nsmul_eq_mul]
  have hodd : ((Finset.Ico 1 (2 * K)).filter Odd).card = K :=
    CFSG.Wreathed.ConditionalSquareRoot.card_filter_odd_Ico K
  have hall := Finset.card_filter_add_card_filter_not (s := Finset.Ico 1 (2 * K)) Odd
  rw [Nat.card_Ico, hodd] at hall
  have heven : ((Finset.Ico 1 (2 * K)).filter fun r => ¬ Odd r).card = K - 1 := by omega
  rw [hodd, heven, Nat.cast_sub (by omega : 1 ≤ K)]
  push_cast
  ring

theorem cubic_sum_value {q ε K Qd C : ℂ} (hq : q ≠ 0) (hQ : Qd ≠ 0) (hqε : q + ε ≠ 0)
    (hC : C ≠ 0) (hQd : Qd = q ^ 2 + ε * q + 1) (hCd : C = q ^ 3 - ε) (hε : ε = 1 ∨ ε = -1) :
    1 + q ^ 3 / q ^ 3 + (2 + ε * q) ^ 3 / Qd + (2 * q + ε) ^ 3 / (q * Qd) +
      (1 + ε * q) ^ 3 / (q * (q + ε)) + 2 * K * ((ε - q) ^ 3 / C) +
      2 * (K * ((-ε * q) ^ 3 / Qd) + (K - 1) * ((2 + ε * q) ^ 3 / Qd)) +
      2 * (K * ((-ε) ^ 3 / (q * Qd)) + (K - 1) * ((2 * q + ε) ^ 3 / (q * Qd))) +
      ((2 * K - 1) * (2 * K - 2) / 6) * ((3 * (q + ε)) ^ 3 / ((q + ε) * Qd)) +
      (4 * K * (4 * K - 2) / 8) * ((-(q + ε)) ^ 3 / ((q + ε) * Qd)) =
    (4 * K) ^ 2 * (q + ε) ^ 2 / Qd := by
  field_simp
  subst hQd hCd
  rcases hε with rfl | rfl <;> ring

theorem BlockFamilies.cubic_sum {p A Bq Dq ω : ι} {M : ℕ} {J : Finset ℕ} {χ : ℕ → ι}
    {γ : ℕ → Fin 4 → ι} {P Q : ℕ → Fin 2 → ι} {m : ℕ} {ψ : ZMod m × ZMod m → ι}
    {V : Finset (ZMod m × ZMod m)} (T : BlockFamilies p A Bq Dq ω M J χ γ P Q ψ V)
    {B : Finset ι}
    (hB : B = ({p, A, Bq, Dq, ω} : Finset ι) ∪ J.image χ ∪
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun re => P re.1 re.2) ∪
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun re => Q re.1 re.2) ∪
      V.image ψ) (F : ι → ℂ) {q ε Qd C : ℂ} {K : ℕ} (hq : q ≠ 0) (hQ : Qd ≠ 0)
    (hqε : q + ε ≠ 0) (hC : C ≠ 0) (hQd : Qd = q ^ 2 + ε * q + 1) (hCd : C = q ^ 3 - ε)
    (hε : ε = 1 ∨ ε = -1) (hK : 1 ≤ K) (hM : M = 2 * K) (hJ : J.card = M)
    (hE : ((V.filter fun I => Even I.1.val ∧ Even I.2.val).card : ℂ) =
      (2 * K - 1) * (2 * K - 2) / 6)
    (hO : ((V.filter fun I => ¬ (Even I.1.val ∧ Even I.2.val)).card : ℂ) =
      4 * K * (4 * K - 2) / 8)
    (Fp : F p = 1) (FA : F A = q ^ 3 / q ^ 3) (FB : F Bq = (2 + ε * q) ^ 3 / Qd)
    (FD : F Dq = (2 * q + ε) ^ 3 / (q * Qd)) (Fω : F ω = (1 + ε * q) ^ 3 / (q * (q + ε)))
    (Fχ : ∀ j ∈ J, F (χ j) = (ε - q) ^ 3 / C)
    (FP : ∀ r ∈ Finset.Ico 1 M, ∀ e,
      F (P r e) = if Odd r then (-ε * q) ^ 3 / Qd else (2 + ε * q) ^ 3 / Qd)
    (FQ : ∀ r ∈ Finset.Ico 1 M, ∀ e,
      F (Q r e) = if Odd r then (-ε) ^ 3 / (q * Qd) else (2 * q + ε) ^ 3 / (q * Qd))
    (Fψ : ∀ I ∈ V, F (ψ I) = if Even I.1.val ∧ Even I.2.val
      then (3 * (q + ε)) ^ 3 / ((q + ε) * Qd) else (-(q + ε)) ^ 3 / ((q + ε) * Qd)) :
    ∑ φ ∈ B, F φ = ((4 * K : ℕ) : ℂ) ^ 2 * (q + ε) ^ 2 / Qd := by
  rw [T.sum_union hB F, Fp, FA, FB, FD, Fω]
  have hχs : ∑ j ∈ J, F (χ j) = 2 * K * ((ε - q) ^ 3 / C) := by
    rw [Finset.sum_congr rfl Fχ, Finset.sum_const, hJ, hM, nsmul_eq_mul]
    push_cast
    ring
  subst hM
  have hPs : ∑ re ∈ Finset.Ico 1 (2 * K) ×ˢ (Finset.univ : Finset (Fin 2)), F (P re.1 re.2) =
      2 * (K * ((-ε * q) ^ 3 / Qd) + ((K : ℂ) - 1) * ((2 + ε * q) ^ 3 / Qd)) := by
    rw [Finset.sum_congr rfl fun re hre => FP re.1 (Finset.mem_product.mp hre).1 re.2]
    exact sum_labels_parity hK _ _ _ fun r e => rfl
  have hQs : ∑ re ∈ Finset.Ico 1 (2 * K) ×ˢ (Finset.univ : Finset (Fin 2)), F (Q re.1 re.2) =
      2 * (K * ((-ε) ^ 3 / (q * Qd)) + ((K : ℂ) - 1) * ((2 * q + ε) ^ 3 / (q * Qd))) := by
    rw [Finset.sum_congr rfl fun re hre => FQ re.1 (Finset.mem_product.mp hre).1 re.2]
    exact sum_labels_parity hK _ _ _ fun r e => rfl
  have hψs : ∑ I ∈ V, F (ψ I) =
      ((2 * K - 1) * (2 * K - 2) / 6) * ((3 * (q + ε)) ^ 3 / ((q + ε) * Qd)) +
        (4 * K * (4 * K - 2) / 8) * ((-(q + ε)) ^ 3 / ((q + ε) * Qd)) := by
    rw [Finset.sum_congr rfl Fψ, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul, hE, hO]
  rw [hχs, hPs, hQs, hψs]
  have key := cubic_sum_value (K := (K : ℂ)) hq hQ hqε hC hQd hCd hε
  have h4K : ((4 * K : ℕ) : ℂ) = 4 * (K : ℂ) := by push_cast; ring
  rw [h4K]
  linear_combination key

theorem modulus_split {n : ℕ} (hn : 2 ≤ n) :
    ∃ K : ℕ, 1 ≤ K ∧ ¬ 3 ∣ K ∧ 2 ^ n / 2 = 2 * K ∧ 2 ^ n = 4 * K := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  refine ⟨2 ^ k, Nat.one_le_two_pow, fun h => ?_, ?_, ?_⟩
  · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  · rw [pow_add]
    norm_num
    omega
  · rw [pow_add]
    norm_num
    ring

theorem cast_even_count {K : ℕ} (hK : 1 ≤ K) (h3 : ¬ 3 ∣ K) :
    (((2 * K - 1) * (2 * K - 2) / 6 : ℕ) : ℂ) = (2 * K - 1) * (2 * K - 2) / 6 := by
  have hdvd : 6 ∣ (2 * K - 1) * (2 * K - 2) := by
    have h2 : 2 * K - 2 = 2 * (K - 1) := by omega
    rw [h2]
    have h3' : 3 ∣ (2 * K - 1) * (K - 1) := by
      have hK3 : K % 3 = 1 ∨ K % 3 = 2 := by omega
      rcases hK3 with h | h
      · exact Dvd.dvd.mul_left (by omega) _
      · exact Dvd.dvd.mul_right (by omega) _
    obtain ⟨c, hc⟩ := h3'
    exact ⟨c, by rw [mul_left_comm, hc]; ring⟩
  rw [Nat.cast_div hdvd (by norm_num), Nat.cast_mul, Nat.cast_sub (by omega),
    Nat.cast_sub (by omega)]
  push_cast
  ring

theorem cast_other_count {K : ℕ} (hK : 1 ≤ K) :
    (((4 * K) * (4 * K - 2) / 8 : ℕ) : ℂ) = 4 * K * (4 * K - 2) / 8 := by
  have hdvd : 8 ∣ (4 * K) * (4 * K - 2) :=
    ⟨K * (2 * K - 1), by
      rw [show 4 * K - 2 = 2 * (2 * K - 1) by omega]
      ring⟩
  rw [Nat.cast_div hdvd (by norm_num), Nat.cast_mul, Nat.cast_sub (by omega)]
  push_cast
  ring

theorem cubic_sum_of_data {p A Bq Dq ω : ι} {n : ℕ} {χ : ℕ → ι} {γ : ℕ → Fin 4 → ι}
    {P Q : ℕ → Fin 2 → ι} {ψ : ZMod (2 ^ n) × ZMod (2 ^ n) → ι}
    {V : Finset (ZMod (2 ^ n) × ZMod (2 ^ n))}
    (T : BlockFamilies p A Bq Dq ω (2 ^ n / 2) ((Finset.Ico 1 (2 ^ n)).filter Odd) χ γ P Q ψ V)
    {B : Finset ι}
    (hB : B = ({p, A, Bq, Dq, ω} : Finset ι) ∪ ((Finset.Ico 1 (2 ^ n)).filter Odd).image χ ∪
      ((Finset.Ico 1 (2 ^ n / 2) ×ˢ (Finset.univ : Finset (Fin 2))).image fun re =>
        P re.1 re.2) ∪
      ((Finset.Ico 1 (2 ^ n / 2) ×ˢ (Finset.univ : Finset (Fin 2))).image fun re =>
        Q re.1 re.2) ∪ V.image ψ)
    (hn : 2 ≤ n) (ch1 chx : ι → ℂ) (deg : ι → ℤ) {q : ℕ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hq : 3 ≤ q) (h1 : ∀ φ, ch1 φ = deg φ) (hp1 : ch1 p = 1)
    (hdA : deg A = (q : ℤ) ^ 3) (hdB : deg Bq = (q : ℤ) ^ 2 + ε * q + 1)
    (hdD : deg Dq = q * ((q : ℤ) ^ 2 + ε * q + 1)) (hdω : deg ω = q * (q + ε))
    (hdχ : ∀ j ∈ (Finset.Ico 1 (2 ^ n)).filter Odd, deg (χ j) = (q : ℤ) ^ 3 - ε)
    (hdPQ : ∀ r ∈ Finset.Ico 1 (2 ^ n / 2), ∀ e', deg (P r e') = (q : ℤ) ^ 2 + ε * q + 1 ∧
      deg (Q r e') = q * ((q : ℤ) ^ 2 + ε * q + 1))
    (hdψ : ∀ I ∈ V, deg (ψ I) = (q + ε) * ((q : ℤ) ^ 2 + ε * q + 1))
    (hx1 : chx p = 1) (hxA : chx A = q) (hxB : chx Bq = 2 + ε * q)
    (hxD : chx Dq = 2 * q + ε) (hxω : chx ω = 1 + ε * q)
    (hxχ : ∀ j ∈ (Finset.Ico 1 (2 ^ n)).filter Odd, chx (χ j) = ε - q)
    (hxPQ : ∀ r ∈ Finset.Ico 1 (2 ^ n / 2), ∀ e',
      chx (P r e') = (if Odd r then -ε * q else 2 + ε * q) ∧
        chx (Q r e') = (if Odd r then -ε else 2 * q + ε))
    (hxψ : ∀ I ∈ V, chx (ψ I) =
      if Even I.1.val ∧ Even I.2.val then 3 * (q + ε) else -(q + ε))
    (hE : (V.filter fun I => Even I.1.val ∧ Even I.2.val).card =
      (2 ^ n / 2 - 1) * (2 ^ n / 2 - 2) / 6)
    (hO : (V.filter fun I => ¬ (Even I.1.val ∧ Even I.2.val)).card = 2 ^ n * (2 ^ n - 2) / 8) :
    ∑ φ ∈ B, chx φ ^ 3 / ch1 φ =
      ((2 ^ n : ℕ) : ℂ) ^ 2 * ((q : ℂ) + ε) ^ 2 / ((q : ℂ) ^ 2 + ε * q + 1) := by
  obtain ⟨K, hK, hK3, hM, hm⟩ := modulus_split hn
  have hq0 : (q : ℂ) ≠ 0 := by
    have : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    exact_mod_cast (show q ≠ 0 by omega)
  have hεC : (ε : ℂ) = 1 ∨ (ε : ℂ) = -1 := by
    rcases hε with h | h <;> rw [h] <;> norm_num
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hQpos : ((q : ℂ) ^ 2 + ε * q + 1) ≠ 0 := by
    have h : ((((q : ℤ) ^ 2 + ε * q + 1 : ℤ) : ℂ)) ≠ 0 := by
      have : (0 : ℤ) < (q : ℤ) ^ 2 + ε * q + 1 := by
        have hq' : (3 : ℤ) ≤ q := by exact_mod_cast hq
        rcases hε with h | h <;> rw [h] <;> nlinarith
      exact_mod_cast this.ne'
    exact_mod_cast h
  have hqε : (q : ℂ) + ε ≠ 0 := by
    have h : (((q : ℤ) + ε : ℤ) : ℂ) ≠ 0 := by
      have : (0 : ℤ) < (q : ℤ) + ε := by
        have hq' : (3 : ℤ) ≤ q := by exact_mod_cast hq
        rcases hε with h | h <;> rw [h] <;> omega
      exact_mod_cast this.ne'
    exact_mod_cast h
  have hC : (q : ℂ) ^ 3 - ε ≠ 0 := by
    have h : ((((q : ℤ) ^ 3 - ε : ℤ)) : ℂ) ≠ 0 := by
      have : (0 : ℤ) < (q : ℤ) ^ 3 - ε := by
        have hq' : (3 : ℤ) ≤ q := by exact_mod_cast hq
        rcases hε with h | h <;> rw [h] <;> nlinarith
      exact_mod_cast this.ne'
    exact_mod_cast h
  have hJ : ((Finset.Ico 1 (2 ^ n)).filter Odd).card = 2 ^ n / 2 := by
    rw [hM, hm, show 4 * K = 2 * (2 * K) by ring]
    exact CFSG.Wreathed.ConditionalSquareRoot.card_filter_odd_Ico (2 * K)
  have hE' : ((V.filter fun I => Even I.1.val ∧ Even I.2.val).card : ℂ) =
      (2 * K - 1) * (2 * K - 2) / 6 := by
    rw [hE, hM]
    exact cast_even_count hK hK3
  have hO' : ((V.filter fun I => ¬ (Even I.1.val ∧ Even I.2.val)).card : ℂ) =
      4 * K * (4 * K - 2) / 8 := by
    rw [hO, hm]
    exact cast_other_count hK
  have key := T.cubic_sum hB (fun φ => chx φ ^ 3 / ch1 φ) hq0 hQpos hqε hC rfl rfl hεC hK hM hJ
    hE' hO'
    (by rw [hx1, hp1]; norm_num)
    (by rw [hxA, h1, hdA]; push_cast; ring)
    (by rw [hxB, h1, hdB]; push_cast; ring)
    (by rw [hxD, h1, hdD]; push_cast; ring)
    (by rw [hxω, h1, hdω]; push_cast; ring)
    (fun j hj => by rw [hxχ j hj, h1, hdχ j hj]; push_cast; ring)
    (fun r hr e' => by
      rw [(hxPQ r hr e').1, h1, (hdPQ r hr e').1]
      split_ifs <;> push_cast <;> ring)
    (fun r hr e' => by
      rw [(hxPQ r hr e').2, h1, (hdPQ r hr e').2]
      split_ifs <;> push_cast <;> ring)
    (fun I hI => by
      rw [hxψ I hI, h1, hdψ I hI]
      split_ifs <;> push_cast <;> ring)
  rw [key, hm]

end CFSG.Wreathed.ConditionalExactOrder
