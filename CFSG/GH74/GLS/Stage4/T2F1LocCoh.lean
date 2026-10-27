module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Group

public section

namespace CFSG.GH74.GLS.Stage4.Rest.F1Loc

private def cohNorm {A : Type*} [CommGroup A] (φ : A →* A) (r : ℕ) : A →* A where
  toFun x := ∏ k ∈ Finset.range r, φ^[k] x
  map_one' := by simp
  map_mul' x y := by simp [Finset.prod_mul_distrib]

private theorem cohNorm_apply {A : Type*} [CommGroup A] (φ : A →* A) (r : ℕ) (x : A) :
    cohNorm φ r x = ∏ k ∈ Finset.range r, φ^[k] x := rfl

private theorem cohNorm_mem {A : Type*} [CommGroup A] (φ : A →* A) (r : ℕ) {B : Subgroup A}
    (hB : ∀ x ∈ B, φ x ∈ B) {y : A} (hy : y ∈ B) : cohNorm φ r y ∈ B := by
  have hit : ∀ k : ℕ, φ^[k] y ∈ B := by
    intro k
    induction k with
    | zero => exact hy
    | succ k ih => rw [Function.iterate_succ_apply']; exact hB _ ih
  rw [cohNorm_apply]
  exact Subgroup.prod_mem _ fun k _ => hit k

private theorem coh_telescope {A : Type*} [CommGroup A] (u : ℕ → A) (m : ℕ) :
    (∏ k ∈ Finset.range m, u (k + 1) ^ k) * (∏ k ∈ Finset.range m, u k) * u m =
      u 0 * (∏ k ∈ Finset.range m, u k ^ k) * u m ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
      pow_succ (u (m + 1)) m]
    calc _ = ((∏ k ∈ Finset.range m, u (k + 1) ^ k) * (∏ k ∈ Finset.range m, u k) * u m) *
          (u (m + 1) ^ m * u (m + 1)) := by ac_rfl
      _ = _ := by rw [ih]; ac_rfl

private theorem coh_twist {A : Type*} [CommGroup A] (φ : A →* A) {r : ℕ}
    (hφr : ∀ x, φ^[r] x = x) {h : A} (hN : cohNorm φ r h = 1) :
    ∃ Y : A, φ Y = Y * h ^ r := by
  refine ⟨∏ k ∈ Finset.range r, (φ^[k] h) ^ k, ?_⟩
  have hT := coh_telescope (fun k => φ^[k] h) r
  have hφY : φ (∏ k ∈ Finset.range r, (φ^[k] h) ^ k) =
      ∏ k ∈ Finset.range r, (φ^[k + 1] h) ^ k := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_pow, Function.iterate_succ_apply']
  have hN' : ∏ k ∈ Finset.range r, φ^[k] h = 1 := hN
  simp only [Function.iterate_zero, id, hφr h, hN', mul_one] at hT
  have h2 : h * φ (∏ k ∈ Finset.range r, (φ^[k] h) ^ k) =
      h * ((∏ k ∈ Finset.range r, (φ^[k] h) ^ k) * h ^ r) := by
    rw [hφY]
    calc _ = (∏ k ∈ Finset.range r, (φ^[k + 1] h) ^ k) * h := by ac_rfl
      _ = _ := by rw [hT]; ac_rfl
  exact mul_left_cancel h2

private theorem coh_twoPart {A : Type*} [CommGroup A] (φ : A →* A) {r e : ℕ} (hr : Odd r)
    (hφr : ∀ x, φ^[r] x = x) {h : A} (hN : cohNorm φ r h = 1) (he : h ^ (2 ^ e) = 1) :
    ∃ x : A, h = x * (φ x)⁻¹ := by
  obtain ⟨Y, hY⟩ := coh_twist φ hφr hN
  have hcop : IsCoprime (r : ℤ) ((2 ^ e : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right e (Nat.coprime_two_right.2 hr))
  obtain ⟨c, d, hcd⟩ := hcop
  have h1 : h = (h ^ r) ^ c := by
    calc h = h ^ (1 : ℤ) := (zpow_one h).symm
      _ = h ^ (c * (r : ℤ) + d * ((2 ^ e : ℕ) : ℤ)) := by rw [hcd]
      _ = (h ^ r) ^ c * (h ^ (2 ^ e)) ^ d := by
        rw [zpow_add, mul_comm c, mul_comm d, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
      _ = (h ^ r) ^ c := by rw [he, one_zpow, mul_one]
  refine ⟨(Y ^ c)⁻¹, ?_⟩
  rw [map_inv, map_zpow, hY, inv_inv, mul_zpow, ← mul_assoc, inv_mul_cancel, one_mul]
  exact h1

private theorem coh_split (A : Type*) [CommGroup A] [Finite A] :
    ∃ (e m : ℕ) (S T : ℤ), Odd m ∧ (∀ a : A, a ^ S * a ^ T = a) ∧
      (∀ a : A, (a ^ S) ^ (2 ^ e) = 1) ∧ (∀ a : A, (a ^ T) ^ m = 1) ∧
      (∀ a : A, a ^ m = 1 → a ^ T = a) := by
  have hn : Nat.card A ≠ 0 := Nat.card_pos.ne'
  obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hcop : IsCoprime (m : ℤ) ((2 ^ e : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right e (Nat.coprime_two_right.2 hm))
  obtain ⟨u, v, huv⟩ := hcop
  have hpow : ∀ (a : A) (w : ℤ), a ^ (w * (Nat.card A : ℤ)) = 1 := by
    intro a w
    rw [zpow_mul, zpow_natCast, pow_card_eq_one']
  have hcard : (Nat.card A : ℤ) = (m : ℤ) * ((2 ^ e : ℕ) : ℤ) := by
    rw [hnm]; push_cast; ring
  refine ⟨e, m, u * m, v * ((2 ^ e : ℕ) : ℤ), hm, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [← zpow_add, huv, zpow_one]
  · intro a
    rw [← zpow_natCast, ← zpow_mul]
    have := hpow a u
    rw [hcard, ← mul_assoc] at this
    exact this
  · intro a
    rw [← zpow_natCast, ← zpow_mul]
    have := hpow a v
    rw [hcard] at this
    have h3 : v * ((2 ^ e : ℕ) : ℤ) * (m : ℤ) = v * ((m : ℤ) * ((2 ^ e : ℕ) : ℤ)) := by ring
    rw [h3]
    exact this
  · intro a ha
    have h1 : a ^ ((u : ℤ) * (m : ℤ)) = 1 := by
      rw [mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]
    have h2 : a ^ ((u : ℤ) * (m : ℤ)) * a ^ (v * ((2 ^ e : ℕ) : ℤ)) = a := by
      rw [← zpow_add, huv, zpow_one]
    rwa [h1, one_mul] at h2

private theorem coh_oddPart {A : Type*} [CommGroup A] (φ : A →* A) {r : ℕ}
    (A₁ A₂ : Subgroup A) (hidx : (A₁ ⊔ A₂).index = 2)
    (hint : ∀ w ∈ A₁ ⊓ A₂, w * w = 1) (hφ₁ : ∀ x ∈ A₁, φ x ∈ A₁) (hφ₂ : ∀ x ∈ A₂, φ x ∈ A₂)
    (h90₁ : ∀ y ∈ A₁, Odd (orderOf y) → cohNorm φ r y = 1 → ∃ x ∈ A₁, y = x * (φ x)⁻¹)
    (h90₂ : ∀ y ∈ A₂, Odd (orderOf y) → cohNorm φ r y = 1 → ∃ x ∈ A₂, y = x * (φ x)⁻¹)
    {m : ℕ} (hm : Odd m) {T : ℤ} (hT : ∀ a : A, a ^ m = 1 → a ^ T = a)
    (hTm : ∀ a : A, (a ^ T) ^ m = 1)
    {h : A} (hhm : h ^ m = 1) (hN : cohNorm φ r h = 1) : ∃ x : A, h = x * (φ x)⁻¹ := by
  have hmem : h ∈ A₁ ⊔ A₂ := by
    have h2 : h ^ 2 ∈ A₁ ⊔ A₂ := by
      have := Subgroup.pow_index_mem (A₁ ⊔ A₂) h
      rwa [hidx] at this
    obtain ⟨k, hk⟩ := hm
    have h1 : h = (h ^ 2) ^ (k + 1) := by
      rw [← pow_mul, show 2 * (k + 1) = m + 1 by omega, pow_succ, hhm, one_mul]
    rw [h1]
    exact Subgroup.pow_mem _ h2 (k + 1)
  obtain ⟨y₁, hy₁, y₂, hy₂, hy⟩ := Subgroup.mem_sup.1 hmem
  obtain ⟨z₁, hz₁def⟩ : ∃ z : A, z = y₁ ^ T := ⟨_, rfl⟩
  obtain ⟨z₂, hz₂def⟩ : ∃ z : A, z = y₂ ^ T := ⟨_, rfl⟩
  have hz₁ : z₁ ∈ A₁ := hz₁def ▸ Subgroup.zpow_mem _ hy₁ T
  have hz₂ : z₂ ∈ A₂ := hz₂def ▸ Subgroup.zpow_mem _ hy₂ T
  have hz : z₁ * z₂ = h := by
    rw [hz₁def, hz₂def, ← mul_zpow, hy, hT h hhm]
  have hz₁m : z₁ ^ m = 1 := hz₁def ▸ hTm y₁
  have hz₂m : z₂ ^ m = 1 := hz₂def ▸ hTm y₂
  have hodd₁ : Odd (orderOf z₁) := hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hz₁m)
  have hodd₂ : Odd (orderOf z₂) := hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hz₂m)
  have hn : cohNorm φ r z₁ * cohNorm φ r z₂ = 1 := by rw [← map_mul, hz, hN]
  have hn₁ : cohNorm φ r z₁ ∈ A₁ := cohNorm_mem φ r hφ₁ hz₁
  have hn₂ : cohNorm φ r z₂ ∈ A₂ := cohNorm_mem φ r hφ₂ hz₂
  have hn₁₂ : cohNorm φ r z₁ ∈ A₂ := by
    have : cohNorm φ r z₁ = (cohNorm φ r z₂)⁻¹ := eq_inv_of_mul_eq_one_left hn
    rw [this]; exact A₂.inv_mem hn₂
  have hsq := hint _ ⟨hn₁, hn₁₂⟩
  have hn₁m : cohNorm φ r z₁ ^ m = 1 := by rw [← map_pow, hz₁m, map_one]
  have hn₁1 : cohNorm φ r z₁ = 1 := by
    obtain ⟨k, hk⟩ := hm
    have : cohNorm φ r z₁ ^ m = cohNorm φ r z₁ := by
      rw [hk, pow_succ, pow_mul, sq, hsq, one_pow, one_mul]
    rw [← this, hn₁m]
  have hn₂1 : cohNorm φ r z₂ = 1 := by rw [hn₁1, one_mul] at hn; exact hn
  obtain ⟨x₁, hx₁, hx₁'⟩ := h90₁ z₁ hz₁ hodd₁ hn₁1
  obtain ⟨x₂, hx₂, hx₂'⟩ := h90₂ z₂ hz₂ hodd₂ hn₂1
  refine ⟨x₁ * x₂, ?_⟩
  rw [← hz, hx₁', hx₂', map_mul, mul_inv]
  ac_rfl

private theorem coh_vanish {A : Type*} [CommGroup A] [Finite A] (φ : A →* A) {r : ℕ} (hr : Odd r)
    (hφr : ∀ x, φ^[r] x = x) (A₁ A₂ : Subgroup A) (hidx : (A₁ ⊔ A₂).index = 2)
    (hint : ∀ w ∈ A₁ ⊓ A₂, w * w = 1) (hφ₁ : ∀ x ∈ A₁, φ x ∈ A₁) (hφ₂ : ∀ x ∈ A₂, φ x ∈ A₂)
    (h90₁ : ∀ y ∈ A₁, Odd (orderOf y) → cohNorm φ r y = 1 → ∃ x ∈ A₁, y = x * (φ x)⁻¹)
    (h90₂ : ∀ y ∈ A₂, Odd (orderOf y) → cohNorm φ r y = 1 → ∃ x ∈ A₂, y = x * (φ x)⁻¹)
    {h : A} (hN : cohNorm φ r h = 1) : ∃ x : A, h = x * (φ x)⁻¹ := by
  obtain ⟨e, m, S, T, hm, hST, hS2, hTm, hT⟩ := coh_split A
  obtain ⟨x₂, hx₂⟩ := coh_twoPart φ hr hφr (h := h ^ S) (by rw [map_zpow, hN, one_zpow]) (hS2 h)
  obtain ⟨xo, hxo⟩ := coh_oddPart φ A₁ A₂ hidx hint hφ₁ hφ₂ h90₁ h90₂ hm hT hTm
    (h := h ^ T) (hTm h) (by rw [map_zpow, hN, one_zpow])
  refine ⟨x₂ * xo, ?_⟩
  rw [map_mul, mul_inv]
  calc h = h ^ S * h ^ T := (hST h).symm
    _ = _ := by rw [hx₂, hxo]; ac_rfl

private def cohConj {G : Type} [Group G] (H : Subgroup G) (f : G)
    (hf : ∀ x ∈ H, f * x * f⁻¹ ∈ H) : H →* H where
  toFun x := ⟨f * x * f⁻¹, hf x x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by
    show f * ((x : G) * y) * f⁻¹ = f * x * f⁻¹ * (f * y * f⁻¹)
    group)

private theorem coh_iter_coe {A G : Type*} [Group A] [Group G] (ι : A →* G) (φ : A →* A) (f : G)
    (hφ : ∀ x, ι (φ x) = f * ι x * f⁻¹) (k : ℕ) (x : A) :
    ι (φ^[k] x) = f ^ k * ι x * (f ^ k)⁻¹ := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, hφ]
    group

private theorem coh_norm_coe {A G : Type*} [CommGroup A] [Group G] (ι : A →* G) (φ : A →* A)
    (f : G) (hφ : ∀ x, ι (φ x) = f * ι x * f⁻¹) (r : ℕ) (x : A) :
    ι (cohNorm φ r x) = ((List.range r).map fun k => f ^ k * ι x * (f ^ k)⁻¹).prod := by
  have key : ∀ n : ℕ, ι (∏ k ∈ Finset.range n, φ^[k] x) =
      ((List.range n).map fun k => f ^ k * ι x * (f ^ k)⁻¹).prod := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, map_mul, ih, List.range_succ, List.map_append, List.prod_append,
        coh_iter_coe ι φ f hφ]
      simp
  exact key r

private theorem coh_cocycle {G : Type*} [Group G] {a f h₀ : G} {r : ℕ} (hfr : f ^ r = 1)
    (hfa : f * a * f⁻¹ = a * h₀) :
    ((List.range r).map fun k => f ^ k * h₀ * (f ^ k)⁻¹).prod = 1 := by
  have key : ∀ n : ℕ, f ^ n * a * (f ^ n)⁻¹ =
      a * ((List.range n).map fun k => f ^ k * h₀ * (f ^ k)⁻¹).prod := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, ← mul_assoc, ← ih]
      calc f ^ (n + 1) * a * (f ^ (n + 1))⁻¹ = f ^ n * (f * a * f⁻¹) * (f ^ n)⁻¹ := by group
        _ = f ^ n * (a * h₀) * (f ^ n)⁻¹ := by rw [hfa]
        _ = _ := by group
  have h := key r
  rw [hfr] at h
  simpa using h

private class CohAbelian {G : Type} [Group G] (H : Subgroup G) : Prop where
  comm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x

private instance cohCommGroup {G : Type} [Group G] (H : Subgroup G) [CohAbelian H] :
    CommGroup H :=
  { (inferInstance : Group H) with
    mul_comm := fun x y => Subtype.ext (CohAbelian.comm (x : G) x.2 (y : G) y.2) }

theorem exists_fixed_in_coset {G : Type} [Group G] [Finite G] {H H₁ H₂ : Subgroup G} {a f z : G}
    {r : ℕ}
    (hHc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hH₁ : H₁ ≤ H) (hH₂ : H₂ ≤ H)
    (hidx : (H₁ ⊔ H₂).relIndex H = 2) (hz : z * z = 1) (hz₁ : H₁ ⊓ H₂ ≤ Subgroup.zpowers z)
    (hfH : ∀ x ∈ H, f * x * f⁻¹ ∈ H) (hfH₁ : ∀ x ∈ H₁, f * x * f⁻¹ ∈ H₁)
    (hfH₂ : ∀ x ∈ H₂, f * x * f⁻¹ ∈ H₂) (hfr : f ^ r = 1) (hr : Odd r)
    (hfa : ∃ h₀ ∈ H, f * a * f⁻¹ = a * h₀)
    (h90₁ : ∀ y ∈ H₁, Odd (orderOf y) →
      ((List.range r).map fun k => f ^ k * y * (f ^ k)⁻¹).prod = 1 →
      ∃ x ∈ H₁, y = x * (f * x * f⁻¹)⁻¹)
    (h90₂ : ∀ y ∈ H₂, Odd (orderOf y) →
      ((List.range r).map fun k => f ^ k * y * (f ^ k)⁻¹).prod = 1 →
      ∃ x ∈ H₂, y = x * (f * x * f⁻¹)⁻¹) :
    ∃ x ∈ H, f * (a * x) * f⁻¹ = a * x := by
  obtain ⟨h₀, hh₀, hfa'⟩ := hfa
  have : CohAbelian H := ⟨hHc⟩
  set φ : H →* H := cohConj H f hfH
  have hφι : ∀ x : H, H.subtype (φ x) = f * H.subtype x * f⁻¹ := fun x => rfl
  have hφr : ∀ x : H, φ^[r] x = x := by
    intro x
    apply Subtype.ext
    have := coh_iter_coe H.subtype φ f hφι r x
    rw [hfr] at this
    simpa using this
  have hnorm : cohNorm φ r ⟨h₀, hh₀⟩ = 1 := by
    apply Subtype.ext
    have h1 := coh_norm_coe H.subtype φ f hφι r ⟨h₀, hh₀⟩
    have h2 : ((List.range r).map fun k => f ^ k * h₀ * (f ^ k)⁻¹).prod = 1 :=
      coh_cocycle hfr hfa'
    exact h1.trans h2
  have hidx' : ((H₁.subgroupOf H) ⊔ (H₂.subgroupOf H)).index = 2 := by
    rw [← Subgroup.subgroupOf_sup hH₁ hH₂]; exact hidx
  have hint : ∀ w ∈ H₁.subgroupOf H ⊓ H₂.subgroupOf H, w * w = 1 := by
    intro w hw
    obtain ⟨hw₁, hw₂⟩ := Subgroup.mem_inf.1 hw
    have hwz : (w : G) ∈ Subgroup.zpowers z :=
      hz₁ (Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hw₁, Subgroup.mem_subgroupOf.1 hw₂⟩)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hwz
    apply Subtype.ext
    show (w : G) * w = 1
    rw [← hk, ← zpow_add, ← two_mul, zpow_mul, zpow_two, hz, one_zpow]
  have hφ₁ : ∀ x ∈ H₁.subgroupOf H, φ x ∈ H₁.subgroupOf H :=
    fun x hx => Subgroup.mem_subgroupOf.2 (hfH₁ _ (Subgroup.mem_subgroupOf.1 hx))
  have hφ₂ : ∀ x ∈ H₂.subgroupOf H, φ x ∈ H₂.subgroupOf H :=
    fun x hx => Subgroup.mem_subgroupOf.2 (hfH₂ _ (Subgroup.mem_subgroupOf.1 hx))
  have h90₁' : ∀ y ∈ H₁.subgroupOf H, Odd (orderOf y) → cohNorm φ r y = 1 →
      ∃ x ∈ H₁.subgroupOf H, y = x * (φ x)⁻¹ := by
    intro y hy hodd hn
    have hyG : (y : G) ∈ H₁ := Subgroup.mem_subgroupOf.1 hy
    have h1 := coh_norm_coe H.subtype φ f hφι r y
    rw [hn, map_one] at h1
    obtain ⟨x, hx, hyx⟩ := h90₁ (y : G) hyG (by rwa [Subgroup.orderOf_coe]) h1.symm
    exact ⟨⟨x, hH₁ hx⟩, Subgroup.mem_subgroupOf.2 hx, Subtype.ext hyx⟩
  have h90₂' : ∀ y ∈ H₂.subgroupOf H, Odd (orderOf y) → cohNorm φ r y = 1 →
      ∃ x ∈ H₂.subgroupOf H, y = x * (φ x)⁻¹ := by
    intro y hy hodd hn
    have hyG : (y : G) ∈ H₂ := Subgroup.mem_subgroupOf.1 hy
    have h1 := coh_norm_coe H.subtype φ f hφι r y
    rw [hn, map_one] at h1
    obtain ⟨x, hx, hyx⟩ := h90₂ (y : G) hyG (by rwa [Subgroup.orderOf_coe]) h1.symm
    exact ⟨⟨x, hH₂ hx⟩, Subgroup.mem_subgroupOf.2 hx, Subtype.ext hyx⟩
  obtain ⟨x, hx⟩ := coh_vanish φ hr hφr _ _ hidx' hint hφ₁ hφ₂ h90₁' h90₂' hnorm
  refine ⟨x, x.2, ?_⟩
  have hx' : h₀ = x * (f * x * f⁻¹)⁻¹ := congrArg Subtype.val hx
  rw [show f * (a * x) * f⁻¹ = (f * a * f⁻¹) * (f * x * f⁻¹) by group, hfa', hx']
  group

end CFSG.GH74.GLS.Stage4.Rest.F1Loc
