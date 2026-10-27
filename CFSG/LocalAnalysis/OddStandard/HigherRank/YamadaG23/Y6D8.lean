module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

variable {G : Type} [Group G] {u t : G}

private lemma y6_basic (hu : orderOf u = 4) (ht : orderOf t = 2)
    (hinv : t * u * t⁻¹ = u⁻¹) :
    u ^ 4 = 1 ∧ t ^ 2 = 1 ∧ t * t = 1 ∧ u⁻¹ = u ^ 3 ∧ t * u = u⁻¹ * t ∧
      t⁻¹ = t ∧ (∀ i : ℕ, t * u ^ i = u ^ (3 * i) * t) := by
  have h4 : u ^ 4 = 1 := by simpa [hu] using pow_orderOf_eq_one u
  have ht2 : t ^ 2 = 1 := by simpa [ht] using pow_orderOf_eq_one t
  have htsq : t * t = 1 := by rw [← pow_two, ht2]
  have huinv : u⁻¹ = u ^ 3 := by
    have h : u ^ 3 * u = 1 := by rw [← pow_succ]; exact h4
    exact inv_eq_of_mul_eq_one_left h
  have htt : t⁻¹ = t := inv_eq_of_mul_eq_one_left htsq
  have htu : t * u = u⁻¹ * t := by
    have h := congrArg (· * t) hinv
    simpa [mul_assoc] using h
  have htupow : ∀ i : ℕ, t * u ^ i = u ^ (3 * i) * t := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, htu, huinv, ← mul_assoc, ← pow_add,
        show 3 * i + 3 = 3 * (i + 1) by rw [Nat.mul_succ]]
  exact ⟨h4, ht2, htsq, huinv, htu, htt, htupow⟩

private lemma y6_normal (ht : orderOf t = 2) (htt : t⁻¹ = t) (huinv : u⁻¹ = u ^ 3)
    (htupow : ∀ i : ℕ, t * u ^ i = u ^ (3 * i) * t) :
    ∀ c ∈ (closure ({u, t} : Set G) : Subgroup G),
      ∃ i : ℕ, ∃ e : ℕ, e < 2 ∧ c = u ^ i * t ^ e := by
  intro c hc
  induction hc using Subgroup.closure_induction_left with
  | one => exact ⟨0, 0, by omega, by simp⟩
  | mul_left x hx y hy ih =>
    obtain ⟨i, e, he, rfl⟩ := ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact ⟨i + 1, e, he, by rw [← mul_assoc, ← pow_succ']⟩
    · rw [hx]
      refine ⟨3 * i, (e + 1) % 2, Nat.mod_lt _ (by omega), ?_⟩
      rw [← mul_assoc, htupow i, mul_assoc, ← pow_succ', ← pow_mod_orderOf t (e + 1), ht]
  | inv_mul_cancel x hx y hy ih =>
    obtain ⟨i, e, he, rfl⟩ := ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact ⟨i + 3, e, he, by
        rw [← mul_assoc, huinv, ← pow_add, show 3 + i = i + 3 by omega]⟩
    · rw [hx]
      refine ⟨3 * i, (e + 1) % 2, Nat.mod_lt _ (by omega), ?_⟩
      rw [htt, ← mul_assoc, htupow i, mul_assoc, ← pow_succ', ← pow_mod_orderOf t (e + 1), ht]

private lemma y6_pow_inj (hu : orderOf u = 4) {i j : Fin 4}
    (h : u ^ (i : ℕ) = u ^ (j : ℕ)) : i = j := by
  apply Fin.ext
  exact pow_injOn_Iio_orderOf (x := u) (by rw [hu]; exact i.2) (by rw [hu]; exact j.2) h

private lemma y6_no_pow_eq_pow_mul_t (hu : orderOf u = 4) (ht : orderOf t = 2)
    (hinv : t * u * t⁻¹ = u⁻¹) {i j : ℕ} (h : u ^ i = u ^ j * t) : False := by
  have htmem : t ∈ zpowers u := by
    have h1 : t = (u ^ j)⁻¹ * u ^ i := by
      rw [h, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h1]
    exact mul_mem (inv_mem (npow_mem_zpowers u j)) (npow_mem_zpowers u i)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp htmem
  have hcomm : t * u = u * t := by
    rw [← hk]
    exact (Commute.zpow_self u k).eq
  have hu_eq : u = u⁻¹ := by
    have h' := hinv
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one] at h'
    exact h'
  have h2 : u ^ 2 = 1 := by
    rw [pow_two]
    exact (mul_eq_one_iff_eq_inv).mpr hu_eq
  have hdvd : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
  rw [hu] at hdvd
  have hle : 4 ≤ 2 := Nat.le_of_dvd (by omega : 0 < 2) hdvd
  omega

private lemma y6_map_zpowers_le {g w : G} (h : g * w * g⁻¹ ∈ zpowers w) :
    (zpowers w).map (MulAut.conj g) ≤ zpowers w := by
  rw [Subgroup.zpowers_eq_closure, MonoidHom.map_closure, Subgroup.closure_le]
  rintro y ⟨z, hz, rfl⟩
  rw [Set.mem_singleton_iff] at hz
  rw [hz]
  simpa [MulAut.conj_apply, Subgroup.zpowers_eq_closure] using h

theorem y6_d8_elems (hu : orderOf u = 4) (ht : orderOf t = 2) (hinv : t * u * t⁻¹ = u⁻¹) :
    ∀ c ∈ (closure ({u, t} : Set G) : Subgroup G), ∃ i : ℕ, c = u ^ i ∨ c = u ^ i * t := by
  obtain ⟨_, _, _, huinv, _, htt, htupow⟩ := y6_basic hu ht hinv
  intro c hc
  obtain ⟨i, e, he, hce⟩ := y6_normal ht htt huinv htupow c hc
  rcases (by omega : e = 0 ∨ e = 1) with he0 | he1
  · rw [he0] at hce
    exact ⟨i, Or.inl (by simpa using hce)⟩
  · rw [he1] at hce
    exact ⟨i, Or.inr (by simpa using hce)⟩

theorem y6_d8_card (hu : orderOf u = 4) (ht : orderOf t = 2) (hinv : t * u * t⁻¹ = u⁻¹) :
    Nat.card ↥(closure ({u, t} : Set G) : Subgroup G) = 8 := by
  let C : Subgroup G := closure ({u, t} : Set G)
  let f : Fin 4 ⊕ Fin 4 → ↥C := fun p =>
    match p with
    | Sum.inl i =>
        ⟨u ^ (i : ℕ), Subgroup.pow_mem C (Subgroup.subset_closure (by simp)) (i : ℕ)⟩
    | Sum.inr i => ⟨u ^ (i : ℕ) * t,
        Subgroup.mul_mem C
          (Subgroup.pow_mem C (Subgroup.subset_closure (by simp)) (i : ℕ))
          (Subgroup.subset_closure (by simp))⟩
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro (i | i) (j | j) h
      · have h' : u ^ (i : ℕ) = u ^ (j : ℕ) := by simpa [f] using congrArg Subtype.val h
        exact congrArg Sum.inl (y6_pow_inj hu h')
      · exfalso
        exact y6_no_pow_eq_pow_mul_t hu ht hinv (by simpa [f] using congrArg Subtype.val h)
      · exfalso
        exact y6_no_pow_eq_pow_mul_t hu ht hinv
          (by simpa [f] using (congrArg Subtype.val h).symm)
      · have h' : u ^ (i : ℕ) * t = u ^ (j : ℕ) * t := by
          simpa [f] using congrArg Subtype.val h
        exact congrArg Sum.inr (y6_pow_inj hu (mul_right_cancel h'))
    · intro c
      obtain ⟨i, hi | hi⟩ := y6_d8_elems hu ht hinv c.val c.2
      · refine ⟨Sum.inl ⟨i % 4, Nat.mod_lt i (by omega)⟩, ?_⟩
        apply Subtype.ext
        change u ^ (i % 4) = c.val
        rw [hi]
        simpa [hu] using pow_mod_orderOf u i
      · refine ⟨Sum.inr ⟨i % 4, Nat.mod_lt i (by omega)⟩, ?_⟩
        apply Subtype.ext
        change u ^ (i % 4) * t = c.val
        rw [hi]
        rw [show u ^ (i % 4) = u ^ i by simpa [hu] using pow_mod_orderOf u i]
  have hcard : Nat.card (Fin 4 ⊕ Fin 4) = Nat.card ↥C := Nat.card_congr (Equiv.ofBijective f hf)
  have h8 : Nat.card (Fin 4 ⊕ Fin 4) = 8 := by
    rw [Nat.card_sum, Nat.card_fin]
  change Nat.card ↥C = 8
  rw [← hcard]
  exact h8

theorem y6_d8_ord4 (hu : orderOf u = 4) (ht : orderOf t = 2) (hinv : t * u * t⁻¹ = u⁻¹) :
    ∀ c ∈ (closure ({u, t} : Set G) : Subgroup G), orderOf c = 4 → c = u ∨ c = u⁻¹ := by
  obtain ⟨h4, _, htsq, huinv, _, htt, htupow⟩ := y6_basic hu ht hinv
  intro c hc hord
  obtain ⟨i, e, he, hce⟩ := y6_normal ht htt huinv htupow c hc
  rcases (by omega : e = 0 ∨ e = 1) with he0 | he1
  · rw [he0] at hce
    have hci : c = u ^ i := by simpa using hce
    rw [hci] at hord ⊢
    have hpmod : u ^ i = u ^ (i % 4) := by simpa [hu] using (pow_mod_orderOf u i).symm
    have hmod : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by
      have := Nat.mod_lt i (by omega : 0 < 4); omega
    rcases hmod with h0 | h1 | h2 | h3
    · exfalso
      have : u ^ i = 1 := by rw [hpmod, h0, pow_zero]
      rw [this, orderOf_one] at hord
      omega
    · left
      rw [hpmod, h1, pow_one]
    · exfalso
      have hpow : u ^ i = u ^ 2 := by rw [hpmod, h2]
      rw [hpow] at hord
      have hsq : (u ^ 2) ^ 2 = 1 := by rw [← pow_mul, show 2 * 2 = 4 by omega, h4]
      have hdvd : orderOf (u ^ 2) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
      rw [hord] at hdvd
      have hle : 4 ≤ 2 := Nat.le_of_dvd (by omega : 0 < 2) hdvd
      omega
    · right
      rw [hpmod, h3]
      exact huinv.symm
  · rw [he1] at hce
    have hci : c = u ^ i * t := by simpa using hce
    rw [hci] at hord
    exfalso
    have hsq : (u ^ i * t) ^ 2 = 1 := by
      rw [pow_two, mul_assoc, ← mul_assoc t (u ^ i) t, htupow i, mul_assoc, htsq, mul_one,
        ← pow_add, show i + 3 * i = 4 * i by omega, pow_mul, h4, one_pow]
    have hdvd : orderOf (u ^ i * t) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
    rw [hord] at hdvd
    have hle : 4 ≤ 2 := Nat.le_of_dvd (by omega : 0 < 2) hdvd
    omega

theorem y6_d8_invol (hu : orderOf u = 4) (ht : orderOf t = 2) (hinv : t * u * t⁻¹ = u⁻¹) :
    ∀ c ∈ (closure ({u, t} : Set G) : Subgroup G), orderOf c = 2 →
      c = u ^ 2 ∨ ∃ i : ℕ, c = u ^ i * t := by
  obtain ⟨_, _, _, huinv, _, htt, htupow⟩ := y6_basic hu ht hinv
  intro c hc hord
  obtain ⟨i, e, he, hce⟩ := y6_normal ht htt huinv htupow c hc
  rcases (by omega : e = 0 ∨ e = 1) with he0 | he1
  · rw [he0] at hce
    have hci : c = u ^ i := by simpa using hce
    rw [hci] at hord ⊢
    have hpmod : u ^ i = u ^ (i % 4) := by simpa [hu] using (pow_mod_orderOf u i).symm
    have hmod : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by
      have := Nat.mod_lt i (by omega : 0 < 4); omega
    rcases hmod with h0 | h1 | h2 | h3
    · exfalso
      have : u ^ i = 1 := by rw [hpmod, h0, pow_zero]
      rw [this, orderOf_one] at hord
      omega
    · exfalso
      have : u ^ i = u := by rw [hpmod, h1, pow_one]
      rw [this, hu] at hord
      omega
    · left
      rw [hpmod, h2]
    · exfalso
      have hii : u ^ i = u ^ 3 := by rw [hpmod, h3]
      rw [hii] at hord
      have h3ord : orderOf (u ^ 3) = 4 := by
        rw [show u ^ 3 = u⁻¹ from huinv.symm, orderOf_inv, hu]
      rw [h3ord] at hord
      omega
  · right
    rw [he1] at hce
    exact ⟨i, by simpa using hce⟩

theorem y6_d8_norm (hu : orderOf u = 4) (ht : orderOf t = 2) (hinv : t * u * t⁻¹ = u⁻¹) :
    ∀ x ∈ normalizer ((closure ({u, t} : Set G) : Subgroup G) : Set G),
      x ∈ normalizer ((zpowers u : Subgroup G) : Set G) := by
  intro x hx
  have hxu : x * u * x⁻¹ ∈ (closure ({u, t} : Set G) : Subgroup G) :=
    (Subgroup.mem_set_normalizer_iff.mp hx u).mp (Subgroup.subset_closure (by simp))
  have hxu4 : orderOf (x * u * x⁻¹) = 4 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hu]
  have hmem : x * u * x⁻¹ ∈ zpowers u := by
    rcases y6_d8_ord4 hu ht hinv (x * u * x⁻¹) hxu hxu4 with h | h
    · rw [h]; exact Subgroup.mem_zpowers u
    · rw [h]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers u)
  have hxinv : x⁻¹ ∈ normalizer ((closure ({u, t} : Set G) : Subgroup G) : Set G) :=
    Subgroup.inv_mem _ hx
  have hxinv_u : x⁻¹ * u * x ∈ (closure ({u, t} : Set G) : Subgroup G) := by
    simpa using
      (Subgroup.mem_set_normalizer_iff.mp hxinv u).mp (Subgroup.subset_closure (by simp))
  have hxinv_u4 : orderOf (x⁻¹ * u * x) = 4 := by
    have h : orderOf ((MulAut.conj x⁻¹) u) = 4 := by rw [MulEquiv.orderOf_eq, hu]
    simpa [MulAut.conj_apply] using h
  have hxinv_mem : x⁻¹ * u * x ∈ zpowers u := by
    rcases y6_d8_ord4 hu ht hinv (x⁻¹ * u * x) hxinv_u hxinv_u4 with h | h
    · rw [h]; exact Subgroup.mem_zpowers u
    · rw [h]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers u)
  have hmap : (zpowers u).map (MulAut.conj x) ≤ zpowers u := y6_map_zpowers_le hmem
  have hmap_inv : (zpowers u).map (MulAut.conj x⁻¹) ≤ zpowers u := by
    apply y6_map_zpowers_le
    simpa using hxinv_mem
  rw [Subgroup.mem_set_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h' : (MulAut.conj x) y ∈ zpowers u := hmap ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using h'
  · intro hy
    have h' : (MulAut.conj x⁻¹) (x * y * x⁻¹) ∈ zpowers u :=
      hmap_inv ⟨x * y * x⁻¹, hy, rfl⟩
    have h'' : (MulAut.conj x⁻¹) (x * y * x⁻¹) = y := by
      rw [MulAut.conj_apply, inv_inv]; simp [mul_assoc]
    rwa [h''] at h'

end CFSG.OddStandard.HigherRank.YamadaG23
