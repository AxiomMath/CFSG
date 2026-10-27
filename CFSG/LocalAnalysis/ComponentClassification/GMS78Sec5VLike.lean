module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5VLikeField

public section

namespace CFSG.ComponentClassification.GMS78.VLike

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

@[expose] def sqMap (a : ℕ) (c e : K) (x : K × K × K) : K :=
  x.1 ^ (2 ^ (a + 1) + 1) + c * (x.1 * x.2.1) ^ 2 ^ a + (e + x.2.2) * x.2.1

@[expose] def commMap (a : ℕ) (c : K) (x y : K × K × K) : K :=
  x.1 * y.1 ^ 2 ^ (a + 1) + x.1 ^ 2 ^ (a + 1) * y.1 +
    c * ((x.1 * y.2.1) ^ 2 ^ a + (y.1 * x.2.1) ^ 2 ^ a) + x.2.2 * y.2.1 + y.2.2 * x.2.1

variable {a : ℕ} {c e : K}

omit [Fintype K] [CharP K 2] in
theorem commMap_snd (x : K × K × K) (r : K) :
    commMap a c x (0, r, 0) = c * (x.1 * r) ^ 2 ^ a + x.2.2 * r := by
  simp [commMap]

omit [Fintype K] [CharP K 2] in
theorem commMap_fst (x : K × K × K) (u : K) :
    commMap a c x (u, 0, 0) =
      x.1 * u ^ 2 ^ (a + 1) + x.1 ^ 2 ^ (a + 1) * u + c * (u * x.2.1) ^ 2 ^ a := by
  simp [commMap]

omit [Fintype K] [CharP K 2] in
theorem commMap_thd (x : K × K × K) (s : K) : commMap a c x (0, 0, s) = s * x.2.1 := by
  simp [commMap]

omit [Fintype K] in
theorem commMap_sub (x z z' : K × K × K) :
    commMap a c x (z - z') = commMap a c x z - commMap a c x z' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simp only [commMap, Prod.fst_sub, Prod.snd_sub, mul_sub, sub_mul, sub_pow_char_pow]
  ring

omit [Fintype K] in
theorem commMap_eq_of_commMap_eq {Λ : AddSubgroup K} {x y : K × K × K}
    (hker : ∀ z : K × K × K, z.2.2 ∈ Λ → commMap a c x z = 0 → commMap a c y z = 0)
    {z z₀ : K × K × K} (hz : z.2.2 ∈ Λ) (hz₀ : z₀.2.2 ∈ Λ)
    (h : commMap a c x z = commMap a c x z₀) : commMap a c y z = commMap a c y z₀ := by
  have h1 : commMap a c x (z - z₀) = 0 := by rw [commMap_sub, h, sub_self]
  have h2 := hker (z - z₀) (by simpa using Λ.sub_mem hz hz₀) h1
  rwa [commMap_sub, sub_eq_zero] at h2


@[expose] def lineHom (a : ℕ) (c : K) (x : K × K × K) : K →+ K where
  toFun r := commMap a c x (0, r, 0)
  map_zero' := by rw [commMap_snd]; simp
  map_add' r r' := by rw [commMap_snd, commMap_snd, commMap_snd, mul_add, add_pow_two_pow]; ring

@[expose] def fstHom (a : ℕ) (c : K) (x : K × K × K) : K →+ K where
  toFun u := commMap a c x (u, 0, 0)
  map_zero' := by rw [commMap_fst]; simp
  map_add' u u' := by
    rw [commMap_fst, commMap_fst, commMap_fst, add_mul, add_pow_two_pow, add_pow_two_pow]
    ring

structure Hyp (a : ℕ) (c e : K) (Λ : AddSubgroup K) (E : AddSubgroup (K × K × K)) : Prop where
  one_le : 1 ≤ a
  card : Fintype.card K = 2 ^ (2 * a + 1)
  four_le : 4 ≤ Nat.card Λ
  mem : ∀ x ∈ E, x.2.2 ∈ Λ
  two : ∃ x ∈ E, ∃ y ∈ E, x ≠ 0 ∧ y ≠ 0 ∧ x ≠ y
  inf : ∀ x ∈ E, x.1 = 0 → x.2.1 = 0 → x = 0
  sq : ∀ x ∈ E, sqMap a c e x = 0
  surj : ∀ x ∈ E, x ≠ 0 → ∀ w : K, ∃ z : K × K × K, z.2.2 ∈ Λ ∧ commMap a c x z = w
  ker : ∀ x ∈ E, ∀ y ∈ E, x ≠ 0 → y ≠ 0 → ∀ z : K × K × K, z.2.2 ∈ Λ →
    commMap a c x z = 0 → commMap a c y z = 0

namespace Hyp

variable {Λ : AddSubgroup K} {E : AddSubgroup (K × K × K)}

omit [Fintype K] in
theorem eq_of_add_eq_zero {x y : K × K × K} (h : x + y = 0) : x = y := by
  have h' : x = -y := eq_neg_of_add_eq_zero_left h
  rw [h']
  ext <;> simp [CharTwo.neg_eq]

omit [CharP K 2] in
theorem snd_ne_zero (h : Hyp a c e Λ E) {x : K × K × K} (hx : x ∈ E) (hx0 : x ≠ 0) :
    x.2.1 ≠ 0 := by
  intro hr
  have hq := h.sq x hx
  simp only [sqMap, hr, mul_zero, zero_pow (pow_pos two_pos a).ne', add_zero] at hq
  exact hx0 (h.inf x hx (pow_eq_zero_iff (by omega) |>.mp hq) hr)

theorem eq_zero_of_const (h : Hyp a c e Λ E) (f : K × K × K → K)
    (hf : ∀ x y, f (x + y) = f x + f y) {x₀ : K × K × K}
    (hc : ∀ y ∈ E, y ≠ 0 → f y = f x₀) : f x₀ = 0 := by
  obtain ⟨x, hx, y, hy, hx0, hy0, hxy⟩ := h.two
  have hxy0 : x + y ≠ 0 := fun h0 => hxy (eq_of_add_eq_zero h0)
  have h1 := hc (x + y) (E.add_mem hx hy) hxy0
  rw [hf, hc x hx hx0, hc y hy hy0] at h1
  have h2 : f x₀ + f x₀ = 0 := CharTwo.add_self_eq_zero _
  rw [h2] at h1
  exact h1.symm

omit [CharP K 2] in
theorem exists_two_lam (h : Hyp a c e Λ E) : ∃ s₁ ∈ Λ, ∃ s₂ ∈ Λ, s₁ ≠ 0 ∧ s₂ ≠ 0 ∧ s₁ ≠ s₂ := by
  classical
  set s := ((Λ : Set K).toFinset).erase 0 with hs_def
  have hs : 1 < s.card := by
    have h4 := h.four_le
    rw [show Nat.card Λ = Nat.card (Λ : Set K) from rfl, Nat.card_eq_card_toFinset] at h4
    rw [hs_def, Finset.card_erase_of_mem (by simp)]
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hs
  simp only [hs_def, Finset.mem_erase, Set.mem_toFinset, SetLike.mem_coe] at hx hy
  exact ⟨x, hx.2, y, hy.2, hx.1, hy.1, hxy⟩

omit [CharP K 2] in
theorem two_pow_lt_card (h : Hyp a c e Λ E) : 2 ^ (a + 1) < (Finset.univ : Finset K).card := by
  rw [Finset.card_univ, h.card]
  exact Nat.pow_lt_pow_right (by norm_num) (by have := h.one_le; omega)

omit [Fintype K] in
theorem eq_of_add_eq_zero' {x y : K} (h : x + y = 0) : x = y := by
  rw [eq_neg_of_add_eq_zero_left h, CharTwo.neg_eq]

theorem commMap_eq_mul_of_c_eq_zero (h : Hyp a 0 e Λ E) {x y : K × K × K} (hx : x ∈ E)
    (hy : y ∈ E) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxs : x.2.2 ≠ 0) {z : K × K × K}
    (hz : z.2.2 ∈ Λ) : commMap a 0 y z = (y.2.2 / x.2.2) * commMap a 0 x z := by
  set w := commMap a 0 x z with hw
  have hz₀ : commMap a 0 x (0, w / x.2.2, 0) = w := by
    rw [commMap_snd]
    field_simp
    ring
  have h1 := commMap_eq_of_commMap_eq (h.ker x hx y hy hx0 hy0) hz (zero_mem Λ) hz₀.symm
  rw [h1, commMap_snd]
  field_simp
  ring

theorem thd_eq_zero_of_c_eq_zero (h : Hyp a 0 e Λ E) : ∀ x ∈ E, x.2.2 = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨x, hx, hxs⟩ := hne
  have hx0 : x ≠ 0 := by rintro rfl; exact hxs rfl
  have hfst : ∀ y ∈ E, y ≠ 0 → y.1 = (y.2.2 / x.2.2) * x.1 ∧
      y.1 ^ 2 ^ (a + 1) = (y.2.2 / x.2.2) * x.1 ^ 2 ^ (a + 1) := by
    intro y hy hy0
    have hv := coeffs_eq_zero_of_vanish h.one_le (α := y.1 - (y.2.2 / x.2.2) * x.1)
      (β := y.1 ^ 2 ^ (a + 1) - (y.2.2 / x.2.2) * x.1 ^ 2 ^ (a + 1)) (γ := 0) Finset.univ
      h.two_pow_lt_card fun u _ => by
        have h1 := h.commMap_eq_mul_of_c_eq_zero hx hy hx0 hy0 hxs (z := (u, 0, 0)) (zero_mem Λ)
        rw [commMap_fst, commMap_fst] at h1
        linear_combination h1
    exact ⟨sub_eq_zero.mp hv.1, sub_eq_zero.mp hv.2.1⟩
  by_cases hu : x.1 = 0
  ·
    have hse : ∀ y ∈ E, y ≠ 0 → y.2.2 = e := by
      intro y hy hy0
      have hy1 : y.1 = 0 := by rw [(hfst y hy hy0).1, hu, mul_zero]
      have hq := h.sq y hy
      simp only [sqMap, hy1, zero_mul, zero_pow (Nat.succ_ne_zero _), zero_add] at hq
      have h2 : e + y.2.2 = 0 := (mul_eq_zero.mp hq).resolve_right (h.snd_ne_zero hy hy0)
      exact (eq_of_add_eq_zero' h2).symm
    exact hxs (h.eq_zero_of_const (fun z => z.2.2) (fun _ _ => rfl) fun y hy hy0 => by
      simp only [hse y hy hy0, hse x hx hx0])
  ·
    have hone : ∀ y ∈ E, y ≠ 0 → y.2.2 = x.2.2 := by
      intro y hy hy0
      obtain ⟨h1, h2⟩ := hfst y hy hy0
      have hρ : (y.2.2 / x.2.2) ^ 2 ^ (a + 1) = y.2.2 / x.2.2 := by
        have h3 : ((y.2.2 / x.2.2) * x.1) ^ 2 ^ (a + 1) = (y.2.2 / x.2.2) * x.1 ^ 2 ^ (a + 1) := by
          rw [← h1, h2]
        rw [mul_pow] at h3
        exact mul_right_cancel₀ (pow_ne_zero _ hu) h3
      rcases eq_zero_or_one_of_pow_two_pow_eq h.card (by have := h.one_le; omega)
        (coprime_a_succ a) hρ with h0 | h1'
      · exfalso
        obtain ⟨z, hz, hz1⟩ := h.surj y hy hy0 1
        rw [h.commMap_eq_mul_of_c_eq_zero hx hy hx0 hy0 hxs hz, h0, zero_mul] at hz1
        exact zero_ne_one hz1
      · exact (div_eq_one_iff_eq hxs).mp h1'
    exact hxs (h.eq_zero_of_const (fun z => z.2.2) (fun _ _ => rfl) hone)

theorem fst_eq_zero_of_c_eq_zero (h : Hyp a 0 e Λ E) : ∀ x ∈ E, x.1 = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨x, hx, hxu⟩ := hne
  have hx0 : x ≠ 0 := by rintro rfl; exact hxu rfl
  have heq : ∀ y ∈ E, y ≠ 0 → y.1 = x.1 := by
    intro y hy hy0
    have hxx : commMap a 0 x (x.1, 0, 0) = 0 := by
      rw [commMap_fst, zero_mul, add_zero, mul_comm (x.1 ^ 2 ^ (a + 1))]
      exact CharTwo.add_self_eq_zero _
    have hyx := h.ker x hx y hy hx0 hy0 (x.1, 0, 0) (zero_mem Λ) hxx
    rw [commMap_fst, zero_mul, add_zero] at hyx
    by_cases hyu : y.1 = 0
    · exfalso
      have hv := coeffs_eq_zero_of_vanish h.one_le (α := x.1) (β := x.1 ^ 2 ^ (a + 1)) (γ := 0)
        Finset.univ h.two_pow_lt_card fun u _ => by
          have h1 := h.ker y hy x hx hy0 hx0 (u, 0, 0) (zero_mem Λ) (by
            rw [commMap_fst, hyu]
            simp)
          rw [commMap_fst, zero_mul, add_zero] at h1
          linear_combination h1
      exact hxu hv.1
    · have hfix : (y.1 / x.1) ^ 2 ^ (a + 1) = y.1 / x.1 := by
        rw [div_pow, div_eq_div_iff (pow_ne_zero _ hxu) hxu]
        linear_combination (eq_of_add_eq_zero' hyx).symm
      rcases eq_zero_or_one_of_pow_two_pow_eq h.card (by have := h.one_le; omega)
        (coprime_a_succ a) hfix with h0 | h1
      · exact absurd (div_eq_zero_iff.mp h0) (by simp [hyu, hxu])
      · exact (div_eq_one_iff_eq hxu).mp h1
  exact hxu (h.eq_zero_of_const (fun z => z.1) (fun _ _ => rfl) heq)

theorem eq_zero_of_c_eq_zero (h : Hyp a 0 e Λ E) :
    e = 0 ∧ Nat.card Λ = Fintype.card K ∧ ∀ x ∈ E, x.1 = 0 ∧ x.2.2 = 0 := by
  have hA := h.thd_eq_zero_of_c_eq_zero
  have hB := h.fst_eq_zero_of_c_eq_zero
  obtain ⟨x, hx, -, -, hx0, -, -⟩ := h.two
  have hxr := h.snd_ne_zero hx hx0
  have hx1 := hB x hx
  have hx3 := hA x hx
  refine ⟨?_, ?_, fun y hy => ⟨hB y hy, hA y hy⟩⟩
  · have hq := h.sq x hx
    simp only [sqMap, hx1, hx3, zero_mul, zero_pow (Nat.succ_ne_zero _), zero_add,
      add_zero] at hq
    exact (mul_eq_zero.mp hq).resolve_right hxr
  · refine le_antisymm ?_ ?_
    · rw [← Nat.card_eq_fintype_card]
      exact Nat.card_le_card_of_injective _ Subtype.val_injective
    · have hsurj : Function.Surjective (fun s : Λ => (s : K) * x.2.1) := fun w => by
        obtain ⟨z, hz, hzw⟩ := h.surj x hx hx0 w
        refine ⟨⟨z.2.2, hz⟩, ?_⟩
        simp only [commMap, hx1, hx3, zero_mul, zero_pow (pow_pos two_pos (a + 1)).ne',
          zero_pow (pow_pos two_pos a).ne', add_zero, zero_add] at hzw
        exact hzw
      rw [← Nat.card_eq_fintype_card]
      exact Nat.card_le_card_of_surjective _ hsurj

theorem fst_ne_zero_of_c_ne_zero (h : Hyp a c e Λ E) (hc : c ≠ 0) {x : K × K × K} (hx : x ∈ E)
    (hx0 : x ≠ 0) : x.1 ≠ 0 := by
  intro hu
  have hσ0 : 2 ^ a ≠ 0 := (pow_pos two_pos a).ne'
  have hθ0 : 2 ^ (a + 1) ≠ 0 := (pow_pos two_pos (a + 1)).ne'
  have hxr := h.snd_ne_zero hx hx0
  obtain ⟨s₁, hs₁, s₂, hs₂, hs₁0, hs₂0, hs12⟩ := h.exists_two_lam
  by_cases hxs : x.2.2 = 0
  ·
    have hzero : ∀ y ∈ E, y ≠ 0 → y.1 = 0 ∧ y.2.2 = 0 := by
      intro y hy hy0
      have hv := coeffs_eq_zero_of_vanish h.one_le (α := 0) (β := y.2.2) (γ := c * y.1 ^ 2 ^ a)
        Finset.univ h.two_pow_lt_card fun r _ => by
          have h1 := h.ker x hx y hy hx0 hy0 (0, r, 0) (zero_mem Λ) (by
            rw [commMap_snd, hu, hxs]
            simp)
          rw [commMap_snd] at h1
          linear_combination h1
      exact ⟨pow_eq_zero_iff hσ0 |>.mp ((mul_eq_zero.mp hv.2.2).resolve_left hc), hv.2.1⟩
    have hr : ∀ y ∈ E, y ≠ 0 → y.2.1 = x.2.1 := by
      intro y hy hy0
      obtain ⟨hy1, hy3⟩ := hzero y hy hy0
      have hyr := h.snd_ne_zero hy hy0
      obtain ⟨t, ht⟩ := pow_two_pow_surjective (K := K) a (s₁ * x.2.1 / c)
      have ht' : t ^ 2 ^ a = s₁ * x.2.1 / c := ht
      set u₀ := t / x.2.1 with hu₀
      have h0 : c * (u₀ * x.2.1) ^ 2 ^ a = s₁ * x.2.1 := by
        rw [hu₀, div_mul_cancel₀ t hxr, ht', mul_div_cancel₀ _ hc]
      have hz : commMap a c x (0, 0, s₁) = commMap a c x (u₀, 0, 0) := by
        rw [commMap_fst, commMap_thd, hu, h0]
        simp
      have h1 := commMap_eq_of_commMap_eq (h.ker x hx y hy hx0 hy0) hs₁ (zero_mem Λ) hz
      rw [commMap_fst, commMap_thd, hy1] at h1
      simp only [zero_mul, zero_pow hθ0, zero_add] at h1
      have h2 : s₁ * (y.2.1 * x.2.1 ^ 2 ^ a) = s₁ * (x.2.1 * y.2.1 ^ 2 ^ a) := by
        linear_combination x.2.1 ^ 2 ^ a * h1 + y.2.1 ^ 2 ^ a * h0
      exact eq_of_pow_two_pow_mul_eq h.one_le h.card hyr hxr
        (by linear_combination -(mul_left_cancel₀ hs₁0 h2))
    exact hxr (h.eq_zero_of_const (fun z => z.2.1) (fun _ _ => rfl) hr)
  ·
    have hy : ∀ y ∈ E, y ≠ 0 → y.1 = 0 := by
      intro y hy hy0
      have hrel : ∀ s' ∈ Λ, s' * y.2.1 =
          c * (y.1 * (s' * x.2.1 / x.2.2)) ^ 2 ^ a + y.2.2 * (s' * x.2.1 / x.2.2) := by
        intro s' hs'
        have hz : commMap a c x (0, 0, s') = commMap a c x (0, s' * x.2.1 / x.2.2, 0) := by
          rw [commMap_thd, commMap_snd, hu]
          field_simp
          simp
        have h1 := commMap_eq_of_commMap_eq (h.ker x hx y hy hx0 hy0) hs' (zero_mem Λ) hz
        rwa [commMap_thd, commMap_snd] at h1
      by_contra hy1
      have hβ : c * y.1 ^ 2 ^ a * (x.2.1 / x.2.2) ^ 2 ^ a ≠ 0 :=
        mul_ne_zero (mul_ne_zero hc (pow_ne_zero _ hy1)) (pow_ne_zero _ (div_ne_zero hxr hxs))
      have e1 := hrel s₁ hs₁
      have e2 := hrel s₂ hs₂
      apply hs12
      refine eq_of_pow_two_pow_mul_eq h.one_le h.card hs₁0 hs₂0 (mul_left_cancel₀ hβ ?_)
      have k1 : s₁ * (y.2.1 - y.2.2 * (x.2.1 / x.2.2)) =
          c * y.1 ^ 2 ^ a * (x.2.1 / x.2.2) ^ 2 ^ a * s₁ ^ 2 ^ a := by
        linear_combination e1
      have k2 : s₂ * (y.2.1 - y.2.2 * (x.2.1 / x.2.2)) =
          c * y.1 ^ 2 ^ a * (x.2.1 / x.2.2) ^ 2 ^ a * s₂ ^ 2 ^ a := by
        linear_combination e2
      linear_combination s₁ * k2 - s₂ * k1
    have hse : ∀ y ∈ E, y ≠ 0 → y.2.2 = e := by
      intro y hy0 hy1
      have hq := h.sq y hy0
      simp only [sqMap, hy y hy0 hy1, zero_mul, zero_pow (Nat.succ_ne_zero _), zero_pow hσ0,
        mul_zero, zero_add] at hq
      exact (eq_of_add_eq_zero' ((mul_eq_zero.mp hq).resolve_right
        (h.snd_ne_zero hy0 hy1))).symm
    exact hxs (h.eq_zero_of_const (fun z => z.2.2) (fun _ _ => rfl) fun y hy hy0 => by
      simp only [hse y hy hy0, hse x hx hx0])

theorem thd_ne_zero_of_c_ne_zero (h : Hyp a c e Λ E) (hc : c ≠ 0) {x : K × K × K} (hx : x ∈ E)
    (hx0 : x ≠ 0) : x.2.2 ≠ 0 := by
  intro hxs
  have hσ0 : 2 ^ a ≠ 0 := (pow_pos two_pos a).ne'
  have hxu := h.fst_ne_zero_of_c_ne_zero hc hx hx0
  have hxr := h.snd_ne_zero hx hx0
  obtain ⟨s₁, hs₁, s₂, hs₂, hs₁0, hs₂0, hs12⟩ := h.exists_two_lam
  have hsol : ∀ w : K, ∃ r₀ : K, commMap a c x (0, r₀, 0) = w := by
    intro w
    obtain ⟨t, ht⟩ := pow_two_pow_surjective (K := K) a (w / c)
    have ht' : t ^ 2 ^ a = w / c := ht
    refine ⟨t / x.1, ?_⟩
    rw [commMap_snd, hxs, mul_div_cancel₀ t hxu, ht', mul_div_cancel₀ _ hc]
    ring
  have hy : ∀ y ∈ E, y ≠ 0 → y.2.2 = 0 ∧ y.2.1 = (y.1 / x.1) ^ 2 ^ a * x.2.1 := by
    intro y hy hy0
    set τ := (y.1 / x.1) ^ 2 ^ a with hτ
    have hτx : τ * x.1 ^ 2 ^ a = y.1 ^ 2 ^ a := by
      rw [hτ, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hxu)]
    have key : ∀ s' ∈ Λ, (y.2.1 - τ * x.2.1) ^ 2 ^ a * (c * x.1 ^ 2 ^ a) * s' ^ 2 ^ a =
        y.2.2 ^ 2 ^ a * x.2.1 * s' := by
      intro s' hs'
      obtain ⟨r₀, h0⟩ := hsol (s' * x.2.1)
      have h1 := commMap_eq_of_commMap_eq (h.ker x hx y hy hx0 hy0) (z := (0, 0, s'))
        (z₀ := (0, r₀, 0)) hs' (zero_mem Λ) (by rw [h0, commMap_thd])
      rw [commMap_thd, commMap_snd] at h1
      rw [commMap_snd, hxs] at h0
      have h2 : y.2.2 * r₀ = s' * (y.2.1 - τ * x.2.1) := by
        have h3 : c * (y.1 * r₀) ^ 2 ^ a = τ * (c * (x.1 * r₀) ^ 2 ^ a) := by
          rw [mul_pow, mul_pow, ← hτx]
          ring
        have h4 : c * (x.1 * r₀) ^ 2 ^ a = s' * x.2.1 := by linear_combination h0
        rw [h3, h4] at h1
        linear_combination -h1
      have h5 := congrArg (· ^ 2 ^ a) h2
      simp only [mul_pow] at h5
      linear_combination (-(c * x.1 ^ 2 ^ a)) * h5 + y.2.2 ^ 2 ^ a * h0
    have hA : (y.2.1 - τ * x.2.1) ^ 2 ^ a * (c * x.1 ^ 2 ^ a) = 0 := by
      by_contra hA
      apply hs12
      refine eq_of_pow_two_pow_mul_eq h.one_le h.card hs₁0 hs₂0 (mul_left_cancel₀ hA ?_)
      linear_combination s₂ * key s₁ hs₁ - s₁ * key s₂ hs₂
    have hD : y.2.1 - τ * x.2.1 = 0 := by
      have := (mul_eq_zero.mp hA).resolve_right (mul_ne_zero hc (pow_ne_zero _ hxu))
      exact pow_eq_zero_iff hσ0 |>.mp this
    have hB : y.2.2 ^ 2 ^ a * x.2.1 * s₁ = 0 := by
      rw [← key s₁ hs₁, hD, zero_pow hσ0, zero_mul, zero_mul]
    refine ⟨?_, sub_eq_zero.mp hD⟩
    have := (mul_eq_zero.mp hB).resolve_right hs₁0
    exact pow_eq_zero_iff hσ0 |>.mp ((mul_eq_zero.mp this).resolve_right hxr)
  have hu : ∀ y ∈ E, y ≠ 0 → y.1 = x.1 := by
    intro y hy0 hy1
    obtain ⟨hys, hyr⟩ := hy y hy0 hy1
    have hyu := h.fst_ne_zero_of_c_ne_zero hc hy0 hy1
    set τ := (y.1 / x.1) ^ 2 ^ a with hτ
    have hτx : τ * x.1 ^ 2 ^ a = y.1 ^ 2 ^ a := by
      rw [hτ, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hxu)]
    have hline : ∀ u : K, commMap a c y (u, 0, 0) = τ * commMap a c x (u, 0, 0) := by
      intro u
      obtain ⟨r₀, h0⟩ := hsol (commMap a c x (u, 0, 0))
      have h1 := commMap_eq_of_commMap_eq (h.ker x hx y hy0 hx0 hy1) (zero_mem Λ) (zero_mem Λ)
        h0.symm
      rw [h1, ← h0, commMap_snd, commMap_snd, hys, hxs, mul_pow, mul_pow, ← hτx]
      ring
    have hv := coeffs_eq_zero_of_vanish h.one_le (α := y.1 - τ * x.1)
      (β := y.1 ^ 2 ^ (a + 1) - τ * x.1 ^ 2 ^ (a + 1))
      (γ := c * (y.2.1 ^ 2 ^ a - τ * x.2.1 ^ 2 ^ a)) Finset.univ h.two_pow_lt_card fun u _ => by
        have h1 := hline u
        rw [commMap_fst, commMap_fst] at h1
        linear_combination h1
    have h2 : y.1 * x.1 ^ 2 ^ a = y.1 ^ 2 ^ a * x.1 := by
      have h3 := sub_eq_zero.mp hv.1
      rw [hτ, div_pow] at h3
      field_simp at h3
      linear_combination h3
    exact eq_of_pow_two_pow_mul_eq h.one_le h.card hyu hxu (by linear_combination -h2)
  exact hxu (h.eq_zero_of_const (fun z => z.1) (fun _ _ => rfl) hu)

omit [CharP K 2] in
theorem exists_pow_two_pow_eq_mul (h : Hyp a c e Λ E) (t : K) :
    ∃ z : K, z ^ 2 ^ a = t * z ∧ (t ≠ 0 → z ≠ 0) := by
  have hσ0 : 2 ^ a ≠ 0 := (pow_pos two_pos a).ne'
  have hinj : Function.Injective fun z : K => z ^ 2 ^ a * z⁻¹ := by
    intro z w hzw
    simp only at hzw
    by_cases hz : z = 0
    · by_cases hw : w = 0
      · rw [hz, hw]
      · exfalso
        rw [hz, zero_pow hσ0, zero_mul, eq_comm, mul_eq_zero, inv_eq_zero] at hzw
        exact hw (hzw.elim (pow_eq_zero_iff hσ0).mp id)
    · by_cases hw : w = 0
      · exfalso
        rw [hw, zero_pow hσ0, zero_mul, mul_eq_zero, inv_eq_zero] at hzw
        exact hz (hzw.elim (pow_eq_zero_iff hσ0).mp id)
      · refine eq_of_pow_two_pow_mul_eq h.one_le h.card hz hw ?_
        field_simp at hzw
        linear_combination hzw
  obtain ⟨z, hz⟩ := (Finite.injective_iff_surjective.mp hinj) t
  simp only at hz
  refine ⟨z, ?_, fun ht hz0 => ht (by rw [← hz, hz0]; simp)⟩
  by_cases hz0 : z = 0
  · rw [hz0, zero_pow hσ0, mul_zero]
  · rw [← hz, mul_assoc, inv_mul_cancel₀ hz0, mul_one]

theorem false_of_c_ne_zero (h : Hyp a c e Λ E) (hc : c ≠ 0)
    (hRu : ¬ (a = 1 ∧ Nat.card Λ = 4)) : False := by
  have hσ0 : 2 ^ a ≠ 0 := (pow_pos two_pos a).ne'
  obtain ⟨x, hx, -, -, hx0, -, -⟩ := h.two
  have hxu := h.fst_ne_zero_of_c_ne_zero hc hx hx0
  have hxs := h.thd_ne_zero_of_c_ne_zero hc hx hx0
  have hxr := h.snd_ne_zero hx hx0
  by_cases hΛ : Nat.card Λ = Fintype.card K
  ·
    have htop : Λ = ⊤ := AddSubgroup.eq_top_of_card_eq Λ (by rw [hΛ, Nat.card_eq_fintype_card])
    have hr : ∀ y ∈ E, y ≠ 0 → y.2.1 = x.2.1 := by
      intro y hy hy0
      have hyr := h.snd_ne_zero hy hy0
      have hline : ∀ u : K,
          commMap a c y (u, 0, 0) = (y.2.1 / x.2.1) * commMap a c x (u, 0, 0) := by
        intro u
        set w := commMap a c x (u, 0, 0) with hw
        have hz₀ : commMap a c x (0, 0, w / x.2.1) = w := by
          rw [commMap_thd, div_mul_cancel₀ _ hxr]
        have h1 := commMap_eq_of_commMap_eq (h.ker x hx y hy hx0 hy0) (zero_mem Λ)
          (by rw [htop]; exact AddSubgroup.mem_top _) hz₀.symm
        rw [h1, commMap_thd]
        field_simp
      have hv := coeffs_eq_zero_of_vanish h.one_le (α := y.1 - (y.2.1 / x.2.1) * x.1)
        (β := y.1 ^ 2 ^ (a + 1) - (y.2.1 / x.2.1) * x.1 ^ 2 ^ (a + 1))
        (γ := c * (y.2.1 ^ 2 ^ a - (y.2.1 / x.2.1) * x.2.1 ^ 2 ^ a)) Finset.univ
        h.two_pow_lt_card fun u _ => by
          have h1 := hline u
          rw [commMap_fst, commMap_fst] at h1
          linear_combination h1
      have h2 := (mul_eq_zero.mp hv.2.2).resolve_left hc
      refine eq_of_pow_two_pow_mul_eq h.one_le h.card hyr hxr ?_
      field_simp at h2
      linear_combination h2
    exact hxr (h.eq_zero_of_const (fun z => z.2.1) (fun _ _ => rfl) hr)
  ·
    have ha2 : 2 ≤ a := by
      by_contra ha
      have ha1 : a = 1 := by have := h.one_le; omega
      apply hRu ⟨ha1, ?_⟩
      have hK8 : Fintype.card K = 8 := by rw [h.card, ha1]; norm_num
      have hdvd : Nat.card Λ ∣ 8 := by
        rw [← hK8, ← Nat.card_eq_fintype_card]
        exact AddSubgroup.card_addSubgroup_dvd_card Λ
      have h4 := h.four_le
      have hle : Nat.card Λ ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
      rw [hK8] at hΛ
      interval_cases hn : Nat.card Λ <;> first | rfl | (exfalso; revert hdvd; decide) | omega
    obtain ⟨ω, hωeq, hω0⟩ := h.exists_pow_two_pow_eq_mul (x.2.2 / (c * x.1 ^ 2 ^ a))
    have hω0' := hω0 (div_ne_zero hxs (mul_ne_zero hc (pow_ne_zero _ hxu)))
    have hcx : c * x.1 ^ 2 ^ a ≠ 0 := mul_ne_zero hc (pow_ne_zero _ hxu)
    have hω : lineHom a c x ω = 0 := by
      change commMap a c x (0, ω, 0) = 0
      have h1 : c * (x.1 ^ 2 ^ a * (x.2.2 / (c * x.1 ^ 2 ^ a) * ω)) = x.2.2 * ω := by
        field_simp
      rw [commMap_snd, mul_pow, hωeq, h1]
      exact CharTwo.add_self_eq_zero _
    have hker : ∀ r, lineHom a c x r = 0 → r = 0 ∨ r = ω := by
      intro r hr
      change commMap a c x (0, r, 0) = 0 at hr
      rw [commMap_snd, mul_pow] at hr
      by_cases hr0 : r = 0
      · exact Or.inl hr0
      · refine Or.inr (eq_of_pow_two_pow_mul_eq h.one_le h.card hr0 hω0' ?_)
        have hr' : c * x.1 ^ 2 ^ a * r ^ 2 ^ a = x.2.2 * r := eq_of_add_eq_zero' (by
          linear_combination hr)
        have hr'' : r ^ 2 ^ a = x.2.2 / (c * x.1 ^ 2 ^ a) * r := by
          rw [div_mul_eq_mul_div, eq_div_iff hcx]
          linear_combination hr'
        rw [hr'', hωeq]
        ring
    have hcard2 : Nat.card (lineHom a c x).ker = 2 := by
      have : ((lineHom a c x).ker : Set K) = {0, ω} := by
        ext r
        simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        refine ⟨hker r, ?_⟩
        rintro (rfl | rfl)
        · exact map_zero _
        · exact hω
      rw [← SetLike.coe_sort_coe, this, Nat.card_coe_set_eq, Set.ncard_pair (Ne.symm hω0')]
    have hrange : Nat.card (lineHom a c x).range * 2 = Fintype.card K := by
      rw [← hcard2, mul_comm, AddSubgroup.card_ker_mul_card_range,
        Nat.card_eq_fintype_card (α := K)]
    set W := (lineHom a c x).range.comap (fstHom a c x) with hW
    have hWcard : 2 ^ (2 * a) ≤ Nat.card W := by
      have hidx : (lineHom a c x).range.index = 2 := by
        have := AddSubgroup.card_mul_index (lineHom a c x).range
        rw [Nat.card_eq_fintype_card (α := K)] at this
        have hpos : 0 < Nat.card (lineHom a c x).range := Nat.card_pos
        have h2 : Nat.card (lineHom a c x).range * (lineHom a c x).range.index =
            Nat.card (lineHom a c x).range * 2 := by rw [this, hrange]
        exact Nat.eq_of_mul_eq_mul_left hpos h2
      have hWidx : W.index ≤ 2 := by
        rw [hW, AddSubgroup.index_comap, ← hidx]
        exact Nat.le_of_dvd (by omega) (AddSubgroup.relIndex_dvd_index_of_normal _ _)
      have := AddSubgroup.card_mul_index W
      rw [Nat.card_eq_fintype_card (α := K), h.card, pow_succ] at this
      nlinarith [Nat.pos_of_ne_zero (AddSubgroup.index_ne_zero_of_finite (H := W))]
    have hu : ∀ y ∈ E, y ≠ 0 → y.1 = x.1 := by
      intro y hy hy0
      have hyu := h.fst_ne_zero_of_c_ne_zero hc hy hy0
      set τ := (y.1 / x.1) ^ 2 ^ a with hτ
      have hτx : τ * x.1 ^ 2 ^ a = y.1 ^ 2 ^ a := by
        rw [hτ, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hxu)]
      have hyω := h.ker x hx y hy hx0 hy0 (0, ω, 0) (zero_mem Λ) hω
      rw [commMap_snd, mul_pow] at hyω
      have hxω : c * x.1 ^ 2 ^ a * ω ^ 2 ^ a = x.2.2 * ω := by
        rw [hωeq]; field_simp
      have hsy : y.2.2 = τ * x.2.2 := by
        refine mul_right_cancel₀ hω0' ?_
        have h1 : c * y.1 ^ 2 ^ a * ω ^ 2 ^ a = y.2.2 * ω :=
          eq_of_add_eq_zero' (by linear_combination hyω)
        rw [← hτx] at h1
        linear_combination -h1 + τ * hxω
      have hline : ∀ r, lineHom a c y r = τ * lineHom a c x r := by
        intro r
        change commMap a c y (0, r, 0) = τ * commMap a c x (0, r, 0)
        rw [commMap_snd, commMap_snd, hsy, mul_pow, mul_pow, ← hτx]
        ring
      have hWeq : ∀ u ∈ W, commMap a c y (u, 0, 0) = τ * commMap a c x (u, 0, 0) := by
        intro u hu
        obtain ⟨r₀, hr₀⟩ := AddSubgroup.mem_comap.mp hu
        have hr₀' : commMap a c x (0, r₀, 0) = commMap a c x (u, 0, 0) := hr₀
        have h1 := commMap_eq_of_commMap_eq (h.ker x hx y hy hx0 hy0) (zero_mem Λ) (zero_mem Λ)
          hr₀'.symm
        rw [h1, ← hr₀']
        exact hline r₀
      classical
      have hv := coeffs_eq_zero_of_vanish h.one_le (α := y.1 - τ * x.1)
        (β := y.1 ^ 2 ^ (a + 1) - τ * x.1 ^ 2 ^ (a + 1))
        (γ := c * (y.2.1 ^ 2 ^ a - τ * x.2.1 ^ 2 ^ a)) (W : Set K).toFinset (by
          rw [← Nat.card_eq_card_toFinset]
          calc 2 ^ (a + 1) < 2 ^ (2 * a) := Nat.pow_lt_pow_right (by norm_num) (by omega)
            _ ≤ Nat.card W := hWcard) fun u hu => by
          have h1 := hWeq u (by simpa using hu)
          rw [commMap_fst, commMap_fst] at h1
          linear_combination h1
      have h2 : y.1 * x.1 ^ 2 ^ a = y.1 ^ 2 ^ a * x.1 := by
        have h3 := sub_eq_zero.mp hv.1
        rw [hτ, div_pow] at h3
        field_simp at h3
        linear_combination h3
      exact eq_of_pow_two_pow_mul_eq h.one_le h.card hyu hxu (by linear_combination -h2)
    exact hxu (h.eq_zero_of_const (fun z => z.1) (fun _ _ => rfl) hu)

theorem eq_zero_of_hyp (h : Hyp a c e Λ E) (hRu : ¬ (a = 1 ∧ Nat.card Λ = 4)) :
    c = 0 ∧ e = 0 ∧ Nat.card Λ = Fintype.card K ∧ ∀ x ∈ E, x.1 = 0 ∧ x.2.2 = 0 := by
  by_cases hc : c = 0
  · subst hc
    exact ⟨rfl, h.eq_zero_of_c_eq_zero⟩
  · exact absurd (h.false_of_c_ne_zero hc hRu) id

end Hyp

end CFSG.ComponentClassification.GMS78.VLike
