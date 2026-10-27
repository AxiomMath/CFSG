module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylModel
public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl
open CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl.ShapeModel

section Shape

variable {X : Type} [Group X] {S A : Subgroup X} {a t y : X} {n : ℕ}

theorem shape_zpow_eq_one_iff {g : X} (hg : orderOf g = 2 ^ n) (k : ℤ) :
    g ^ k = 1 ↔ (2 : ℤ) ^ n ∣ k := by
  rw [← orderOf_dvd_iff_zpow_eq_one, hg]
  push_cast
  rfl

theorem shape_not_dvd_two (hn : 2 ≤ n) : ¬ ((2 : ℤ) ^ n ∣ 2) := by
  intro hd
  have h1 : (2 : ℤ) ^ n ≤ 2 := Int.le_of_dvd (by norm_num) hd
  have h2 : (2 : ℤ) ^ 2 ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  norm_num at h2
  omega

theorem shape_mul_self_ne_one {g : X} (hg : orderOf g = 2 ^ n) (hn : 2 ≤ n) : g * g ≠ 1 := by
  intro h
  have h2 : g ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact h
  exact shape_not_dvd_two hn ((shape_zpow_eq_one_iff hg 2).1 h2)

theorem shape_unique {a b : X} (hdis : ∀ i j : ℤ, a ^ i = b ^ j → a ^ i = 1) {i j k l : ℤ}
    (h : a ^ i * b ^ j = a ^ k * b ^ l) : a ^ i = a ^ k ∧ b ^ j = b ^ l := by
  have h1 : a ^ (i - k) = b ^ (l - j) := by
    calc a ^ (i - k) = (a ^ k)⁻¹ * (a ^ i * b ^ j) * (b ^ j)⁻¹ := by group
      _ = (a ^ k)⁻¹ * (a ^ k * b ^ l) * (b ^ j)⁻¹ := by rw [h]
      _ = b ^ (l - j) := by group
  have h2 := hdis _ _ h1
  rw [h2] at h1
  constructor
  · rw [zpow_sub] at h2
    exact mul_inv_eq_one.1 h2
  · have h3 : b ^ (l - j) = 1 := h1.symm
    rw [zpow_sub] at h3
    exact (mul_inv_eq_one.1 h3).symm

theorem shape_prod {a b : X} (hdis : ∀ i j : ℤ, a ^ i = b ^ j → a ^ i = 1) {i j : ℤ}
    (h : a ^ i * b ^ j = 1) : a ^ i = 1 ∧ b ^ j = 1 := by
  have := shape_unique hdis (i := i) (j := j) (k := 0) (l := 0) (by simpa using h)
  simpa using this

theorem shape_AA {a b : X} (hab : Commute a b) (i j : ℤ) :
    a ^ i * b ^ j * (a ^ i * b ^ j) = a ^ (i + i) * b ^ (j + j) := by
  have hc : Commute (b ^ j) (a ^ i) := (hab.zpow_zpow i j).symm
  rw [zpow_add, zpow_add]
  exact hc.mul_mul_mul_comm _ _

theorem shape_half {i : ℤ} (hn : 1 ≤ n) (h : (2 : ℤ) ^ n ∣ i + i) :
    ∃ k : ℤ, i = 2 ^ (n - 1) * k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  rw [pow_succ] at hc
  rw [Nat.add_sub_cancel]
  linarith

theorem shape_even {i : ℤ} (hn : 2 ≤ n) (h : (2 : ℤ) ^ n ∣ i + i) : ∃ i' : ℤ, i = i' + i' := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨c, hc⟩ := h
  refine ⟨2 ^ m * c, ?_⟩
  rw [pow_add] at hc
  linarith

theorem shape_y_comm {y u : X} (hyy : y * y = 1) (huu : u * u = 1) (hy : y * u * y = u⁻¹) :
    y * u = u * y := by
  have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  rw [hu] at hy
  calc y * u = y * u * (y * y) := by rw [hyy, mul_one]
    _ = (y * u * y) * y := by rw [mul_assoc (y * u) y y]
    _ = u * y := by rw [hy]

theorem shape_cancel_A {x a τ : X} (hxa : x * a = a * x) (h : a * (x * τ) = x * τ * a) :
    τ * a = a * τ := by
  have : x * (a * τ) = x * (τ * a) := by
    calc x * (a * τ) = x * a * τ := (mul_assoc _ _ _).symm
      _ = a * x * τ := by rw [hxa]
      _ = a * (x * τ) := mul_assoc _ _ _
      _ = x * τ * a := h
      _ = x * (τ * a) := mul_assoc _ _ _
  exact (mul_left_cancel this).symm

theorem shape_four_distinct {a b : X} (hdis : ∀ i j : ℤ, a ^ i = b ^ j → a ^ i = 1)
    (ha2 : a * a ≠ 1) (hb2 : b * b ≠ 1) :
    (1 : X) ≠ a * a ∧ (1 : X) ≠ b * b ∧ (1 : X) ≠ a * a * (b * b) ∧ a * a ≠ b * b ∧
      a * a ≠ a * a * (b * b) ∧ b * b ≠ a * a * (b * b) := by
  refine ⟨fun h => ha2 h.symm, fun h => hb2 h.symm, ?_, ?_, ?_, ?_⟩
  · intro h
    apply ha2
    have h1 : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left h.symm
    have h2 := hdis 2 (-2) (by rw [zpow_neg, zpow_two, zpow_two, h1])
    rwa [zpow_two] at h2
  · intro h
    apply ha2
    have h2 := hdis 2 2 (by rw [zpow_two, zpow_two, h])
    rwa [zpow_two] at h2
  · intro h
    apply hb2
    exact (mul_eq_left.1 h.symm)
  · intro h
    apply ha2
    exact (mul_eq_right.1 h.symm)

theorem shape_card_four {U : Subgroup X} (hc : Nat.card U = 4) {p q r s : X} (hp : p ∈ U)
    (hq : q ∈ U) (hr : r ∈ U) (hs : s ∈ U) (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) : ∀ u ∈ U, u = p ∨ u = q ∨ u = r ∨ u = s := by
  intro u hu
  have hfin : (U : Set X).Finite := by
    have : Finite U := Nat.finite_of_card_ne_zero (by omega)
    exact Set.toFinite _
  have hsub : ({p, q, r, s} : Set X) ⊆ U := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> assumption
  have hcard : (U : Set X).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact hc
  have hs4 : ({p, q, r, s} : Set X).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hrs]
    · simp [hqr, hqs]
    · simp [hpq, hpr, hps]
  have heq := Set.eq_of_subset_of_ncard_le hsub (by omega) hfin
  have : u ∈ ({p, q, r, s} : Set X) := heq ▸ hu
  simpa using this

theorem shape_mem_sup {H K : Subgroup X} (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : X}
    (hx : x ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, K.one_mem, (mul_one x).symm⟩
    · exact ⟨1, H.one_mem, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, H.one_mem, 1, K.one_mem, (mul_one 1).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨h₁, hh₁, k₁, hk₁, rfl⟩ := hx
    obtain ⟨h₂, hh₂, k₂, hk₂, rfl⟩ := hy
    refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
    have := hc h₂ hh₂ k₁ hk₁
    calc h₁ * k₁ * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
      _ = h₁ * (h₂ * k₁) * k₂ := by rw [← this]
      _ = h₁ * h₂ * (k₁ * k₂) := by group
  | inv x _ hx =>
    obtain ⟨h, hh, k, hk, rfl⟩ := hx
    refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
    have hcm : Commute h k := hc h hh k hk
    rw [mul_inv_rev]
    exact (Commute.inv_inv hcm).eq.symm

theorem shape_data (h : ShapeConds S A a t y n) : ShapeData n a (t⁻¹ * a * t) t y := by
  obtain ⟨ha, hA, hab, hcomm, htt, hyy, hty, ht1, hy1, hty', hAty, hyA, hS⟩ := h
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hsemi : SemiconjBy t⁻¹ a (t⁻¹ * a * t) := (mul_inv_cancel_right (t⁻¹ * a) t).symm
  have hb_ord : orderOf (t⁻¹ * a * t) = 2 ^ n := by rw [← hsemi.orderOf_eq, ha]
  have ha_mem : a ∈ A := by rw [hA]; exact mem_sup_left (mem_zpowers a)
  have hb_mem : t⁻¹ * a * t ∈ A := by rw [hA]; exact mem_sup_right (mem_zpowers _)
  exact
    { a_pow := by rw [← ha]; exact pow_orderOf_eq_one a
      b_pow := by rw [← hb_ord]; exact pow_orderOf_eq_one _
      ab := hcomm
      t_sq := by rw [pow_two]; exact htt
      y_sq := by rw [pow_two]; exact hyy
      ty := hty
      tab := by rw [hti]
      tba := by simp [mul_assoc]
      ya := by rw [hyi]; exact hyA a ha_mem
      yb := by rw [hyi]; exact hyA _ hb_mem }

theorem shape_A_eq (h : ShapeConds S A a t y n) : A = (shape_data h).fN.range := by
  rw [(shape_data h).fN_range]; exact h.2.1

theorem shape_S_eq (h : ShapeConds S A a t y n) : S = (shape_data h).lift.range := by
  have hD := shape_data h
  rw [hD.lift_range, hD.fN_range, hD.fH_range, ← h.2.1]
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.trans (sup_assoc _ _ _)

theorem shape_core (h : ShapeConds S A a t y n) :
    ∃ b : X, ShapeData n a b t y ∧ orderOf b = 2 ^ n ∧ (∀ i j : ℤ, a ^ i = b ^ j → a ^ i = 1) ∧
      (∀ x, x ∈ A ↔ ∃ i j : ℤ, x = a ^ i * b ^ j) ∧ (∀ x ∈ A, ∀ x' ∈ A, x * x' = x' * x) := by
  have hD := shape_data h
  refine ⟨t⁻¹ * a * t, hD, ?_, ?_, ?_, ?_⟩
  · have hsemi : SemiconjBy t⁻¹ a (t⁻¹ * a * t) := (mul_inv_cancel_right (t⁻¹ * a) t).symm
    rw [← hsemi.orderOf_eq, h.1]
  · intro i j hij
    have hmem : a ^ i ∈ zpowers a ⊓ zpowers (t⁻¹ * a * t) :=
      ⟨mem_zpowers_iff.2 ⟨i, rfl⟩, mem_zpowers_iff.2 ⟨j, hij.symm⟩⟩
    rw [h.2.2.1] at hmem
    exact mem_bot.1 hmem
  · intro x
    constructor
    · intro hx
      rw [shape_A_eq h] at hx
      obtain ⟨⟨z₁, z₂⟩, rfl⟩ := hx
      obtain ⟨i, rfl⟩ := exists_intCast _ z₁
      obtain ⟨j, rfl⟩ := exists_intCast _ z₂
      refine ⟨i, j, ?_⟩
      rw [hD.fN_apply]
      simp only [cycHom_intCast]
    · rintro ⟨i, j, rfl⟩
      rw [h.2.1]
      exact mul_mem (mem_sup_left (zpow_mem (mem_zpowers a) i))
        (mem_sup_right (zpow_mem (mem_zpowers _) j))
  · intro x hx x' hx'
    rw [shape_A_eq h] at hx hx'
    obtain ⟨z, rfl⟩ := hx
    obtain ⟨z', rfl⟩ := hx'
    rw [← map_mul, ← map_mul, mul_comm z z']

theorem ShapeConds.le_S (h : ShapeConds S A a t y n) : A ≤ S ∧ t ∈ S ∧ y ∈ S := by
  have hS := h.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · rw [hS]; exact le_sup_left.trans le_sup_left
  · rw [hS]; exact mem_sup_left (mem_sup_right (mem_zpowers t))
  · rw [hS]; exact mem_sup_right (mem_zpowers y)

theorem ShapeConds.A_comm (h : ShapeConds S A a t y n) : ∀ x ∈ A, ∀ x' ∈ A, x * x' = x' * x :=
  (shape_core h).choose_spec.2.2.2.2

theorem ShapeConds.decomp (h : ShapeConds S A a t y n) {s : X} (hs : s ∈ S) :
    ∃ x ∈ A, s = x ∨ s = x * t ∨ s = x * y ∨ s = x * t * y := by
  have hD := shape_data h
  have htt : t * t = 1 := h.2.2.2.2.1
  have hyy : y * y = 1 := h.2.2.2.2.2.1
  rw [shape_S_eq h] at hs
  obtain ⟨⟨z, w⟩, rfl⟩ := hs
  rw [hD.lift_apply]
  have hxA : hD.fN z ∈ A := by rw [shape_A_eq h]; exact ⟨z, rfl⟩
  have hw : hD.fH w ∈ zpowers t ⊔ zpowers y := by rw [← hD.fH_range]; exact ⟨w, rfl⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := shape_mem_sup (fun p hp q hq => by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hp
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hq
    exact (hD.ty.zpow_zpow i j).eq) hw
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hp
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hq
  refine ⟨hD.fN z, hxA, ?_⟩
  rw [hpq]
  rcases zpow_eq_one_or_self htt i with hk | hk <;> rcases zpow_eq_one_or_self hyy j with hl | hl
  · left; rw [hk, hl, mul_one, mul_one]
  · right; right; left; rw [hk, hl, one_mul]
  · right; left; rw [hk, hl, mul_one]
  · right; right; right; rw [hk, hl]; exact (mul_assoc _ _ _).symm

theorem ShapeConds.four_sq (h : ShapeConds S A a t y n) (hn : 2 ≤ n) {U : Subgroup X}
    (hUS : U ≤ S) (hU : IVK.IsFourSubgroup U)
    (hUn : ∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U) : ∀ u ∈ U, ∃ x ∈ A, u = x * x := by
  obtain ⟨b, hD, hbo, hdis, hAmem, hAcomm⟩ := shape_core h
  have hAS := (ShapeConds.le_S h).1
  have haA : a ∈ A := (hAmem a).2 ⟨1, 0, by simp⟩
  have hbA : b ∈ A := (hAmem b).2 ⟨0, 1, by simp⟩
  have hh := h
  obtain ⟨hao, -, -, -, htt, hyy, -, -, -, -, -, hyA, -⟩ := h
  have := hU.1
  have hsq : ∀ u ∈ U, u * u = 1 := fun u hu => by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) u hu
    rwa [pow_two] at this
  have hcomm : ∀ a' ∈ A, ∀ u ∈ U, a' * u * a'⁻¹ * u⁻¹ ∈ U := fun a' ha' u hu =>
    mul_mem (hUn a' (hAS ha') u hu) (inv_mem hu)
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  intro u hu
  obtain ⟨x, hx, hxu⟩ := ShapeConds.decomp hh (hUS hu)
  rcases hxu with rfl | rfl | rfl | rfl
  ·
    obtain ⟨i, j, rfl⟩ := (hAmem u).1 hx
    have hxx := hsq _ hu
    rw [shape_AA hD.ab] at hxx
    obtain ⟨h1, h2⟩ := shape_prod hdis hxx
    obtain ⟨i', hi'⟩ := shape_even hn ((shape_zpow_eq_one_iff hao _).1 h1)
    obtain ⟨j', hj'⟩ := shape_even hn ((shape_zpow_eq_one_iff hbo _).1 h2)
    refine ⟨a ^ i' * b ^ j', (hAmem _).2 ⟨i', j', rfl⟩, ?_⟩
    rw [shape_AA hD.ab, hi', hj']
  ·
    exfalso
    have hc := hcomm a haA _ hu
    have e1 : t * a⁻¹ * t⁻¹ = b⁻¹ := by
      calc t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ := by group
        _ = b⁻¹ := by rw [hD.tab]
    have hxb : x * b⁻¹ * x⁻¹ = b⁻¹ := by
      rw [hAcomm x hx b⁻¹ (inv_mem hbA)]; group
    have e2 : a * (x * t) * a⁻¹ * (x * t)⁻¹ = a * b⁻¹ := by
      calc a * (x * t) * a⁻¹ * (x * t)⁻¹ = a * (x * (t * a⁻¹ * t⁻¹) * x⁻¹) := by group
        _ = a * (x * b⁻¹ * x⁻¹) := by rw [e1]
        _ = a * b⁻¹ := by rw [hxb]
    rw [e2] at hc
    have hsq1 := hsq _ hc
    have := shape_AA hD.ab 1 (-1)
    simp only [zpow_one, zpow_neg_one] at this
    rw [this] at hsq1
    obtain ⟨h1, -⟩ := shape_prod hdis hsq1
    have h3 := (shape_zpow_eq_one_iff hao _).1 h1
    norm_num at h3
    exact shape_not_dvd_two hn h3
  ·
    have e3 : ∀ g ∈ A, g * (x * y) * g⁻¹ * (x * y)⁻¹ = g * g := by
      intro g hg
      have e : y * g⁻¹ * y⁻¹ = g := by
        calc y * g⁻¹ * y⁻¹ = (y * g * y⁻¹)⁻¹ := by group
          _ = g := by rw [hyi, hyA g hg, inv_inv]
      calc g * (x * y) * g⁻¹ * (x * y)⁻¹ = g * (x * (y * g⁻¹ * y⁻¹) * x⁻¹) := by group
        _ = g * (x * g * x⁻¹) := by rw [e]
        _ = g * g := by rw [hAcomm x hx g hg]; group
    have haa : a * a ∈ U := by
      have := hcomm a haA _ hu
      rwa [e3 a haA] at this
    have hbb : b * b ∈ U := by
      have := hcomm b hbA _ hu
      rwa [e3 b hbA] at this
    have habab : a * a * (b * b) ∈ U := mul_mem haa hbb
    obtain ⟨d12, d13, d14, d23, d24, d34⟩ :=
      shape_four_distinct hdis (shape_mul_self_ne_one hao hn) (shape_mul_self_ne_one hbo hn)
    rcases shape_card_four hU.2 (one_mem U) haa hbb habab d12 d13 d14 d23 d24 d34 _ hu with
      h1 | h1 | h1 | h1
    · exact ⟨1, one_mem _, by rw [h1, mul_one]⟩
    · exact ⟨a, haA, h1⟩
    · exact ⟨b, hbA, h1⟩
    · exact ⟨a * b, mul_mem haA hbA, by rw [h1, hD.ab.symm.mul_mul_mul_comm a b]⟩
  ·
    exfalso
    have hc := hcomm a haA _ hu
    have e1 : y * a⁻¹ * y⁻¹ = a := by
      calc y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
        _ = a := by rw [hD.ya, inv_inv]
    have e2 : a * (x * t * y) * a⁻¹ * (x * t * y)⁻¹ = a * b := by
      calc a * (x * t * y) * a⁻¹ * (x * t * y)⁻¹
          = a * (x * (t * (y * a⁻¹ * y⁻¹) * t⁻¹) * x⁻¹) := by group
        _ = a * (x * (t * a * t⁻¹) * x⁻¹) := by rw [e1]
        _ = a * (x * b * x⁻¹) := by rw [hD.tab]
        _ = a * b := by rw [hAcomm x hx b hbA]; group
    rw [e2] at hc
    have hsq1 := hsq _ hc
    have := shape_AA hD.ab 1 1
    simp only [zpow_one] at this
    rw [this] at hsq1
    obtain ⟨h1, -⟩ := shape_prod hdis hsq1
    have h3 := (shape_zpow_eq_one_iff hao _).1 h1
    norm_num at h3
    exact shape_not_dvd_two hn h3

theorem ShapeConds.central_invols (h : ShapeConds S A a t y n) (hn : 2 ≤ n) {M : Subgroup X}
    (hMS : M ≤ S) (hM2 : M.relIndex S = 2) (hinv : ∀ g ∈ S, orderOf g = 2 → g ∈ M) :
    ∃ u₁ u₂ : X, u₁ ∈ S ∧ u₂ ∈ S ∧ orderOf u₁ = 2 ∧ orderOf u₂ = 2 ∧ u₁ ≠ u₂ ∧
      ∀ m ∈ M, m * u₁ = u₁ * m ∧ m * u₂ = u₂ * m := by
  obtain ⟨b, hD, hbo, hdis, hAmem, hAcomm⟩ := shape_core h
  obtain ⟨hAS, htS, hyS⟩ := ShapeConds.le_S h
  have haA : a ∈ A := (hAmem a).2 ⟨1, 0, by simp⟩
  have hbA : b ∈ A := (hAmem b).2 ⟨0, 1, by simp⟩
  have hh := h
  obtain ⟨hao, -, -, -, htt, hyy, -, -, hy1, -, hAty, hyA, hS⟩ := h
  have hyA' : y ∉ A := by
    intro hy
    have : y ∈ A ⊓ (zpowers t ⊔ zpowers y) := ⟨hy, mem_sup_right (mem_zpowers y)⟩
    rw [hAty] at this
    exact hy1 (mem_bot.1 this)
  have hyM : y ∈ M := hinv y hyS (orderOf_eq_prime (by rw [pow_two]; exact hyy) hy1)
  have hAM : ∀ x ∈ A, x ∈ M := by
    intro x hx
    have hxy : x * y ∈ M := by
      apply hinv _ (mul_mem (hAS hx) hyS)
      apply orderOf_eq_prime
      · rw [pow_two]
        calc x * y * (x * y) = x * (y * x * y) := by group
          _ = 1 := by rw [hyA x hx]; group
      · intro h1
        apply hyA'
        have : y = x⁻¹ := eq_inv_of_mul_eq_one_right h1
        rw [this]
        exact inv_mem hx
    have := mul_mem hxy (inv_mem hyM)
    simpa using this
  have htM : t ∉ M := by
    intro htM
    have hSM : S ≤ M := by
      rw [hS]
      refine sup_le (sup_le (fun x hx => hAM x hx) ?_) ?_
      · rw [zpowers_le]; exact htM
      · rw [zpowers_le]; exact hyM
    have h1 : M.relIndex S = 1 := relIndex_eq_one.2 hSM
    omega
  have hMshape : ∀ m ∈ M, ∃ x ∈ A, m = x ∨ m = x * y := by
    intro m hm
    obtain ⟨x, hx, hm'⟩ := ShapeConds.decomp hh (hMS hm)
    refine ⟨x, hx, ?_⟩
    rcases hm' with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exfalso
      apply htM
      have : t = x⁻¹ * m := by rw [h1]; group
      rw [this]
      exact mul_mem (inv_mem (hAM x hx)) hm
    · exact Or.inr h1
    · exfalso
      apply htM
      have : t = x⁻¹ * m * y⁻¹ := by rw [h1]; group
      rw [this]
      exact mul_mem (mul_mem (inv_mem (hAM x hx)) hm) (inv_mem hyM)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hord : ∀ g : X, orderOf g = 2 ^ (k + 1) → orderOf (g ^ 2 ^ k) = 2 := by
    intro g hg
    rw [orderOf_pow_of_dvd (by positivity) (hg ▸ Nat.pow_dvd_pow 2 (Nat.le_succ k)), hg,
      pow_succ, Nat.mul_div_cancel_left _ (by positivity)]
  have hsqu : ∀ g : X, orderOf g = 2 ^ (k + 1) → g ^ 2 ^ k * g ^ 2 ^ k = 1 := by
    intro g hg
    rw [← pow_two, ← pow_mul, ← pow_succ, ← hg]
    exact pow_orderOf_eq_one g
  have hu₁ : a ^ 2 ^ k ∈ A := pow_mem haA _
  have hu₂ : b ^ 2 ^ k ∈ A := pow_mem hbA _
  have hcm : ∀ u ∈ A, u * u = 1 → ∀ m ∈ M, m * u = u * m := by
    intro u hu huu m hm
    obtain ⟨x, hx, h1 | h1⟩ := hMshape m hm
    · rw [h1]; exact hAcomm x hx u hu
    · rw [h1]
      have hyu := shape_y_comm hyy huu (hyA u hu)
      calc x * y * u = x * (y * u) := mul_assoc _ _ _
        _ = x * (u * y) := by rw [hyu]
        _ = x * u * y := (mul_assoc _ _ _).symm
        _ = u * x * y := by rw [hAcomm x hx u hu]
        _ = u * (x * y) := mul_assoc _ _ _
  refine ⟨a ^ 2 ^ k, b ^ 2 ^ k, hAS hu₁, hAS hu₂, hord a hao, hord b hbo, ?_, fun m hm => ?_⟩
  · intro heq
    have h1 : a ^ ((2 ^ k : ℕ) : ℤ) = 1 := by
      apply hdis _ ((2 ^ k : ℕ) : ℤ)
      rw [zpow_natCast, zpow_natCast]
      exact heq
    rw [zpow_natCast] at h1
    have := hord a hao
    rw [h1, orderOf_one] at this
    omega
  · exact ⟨hcm _ hu₁ (hsqu a hao) m hm, hcm _ hu₂ (hsqu b hbo) m hm⟩

theorem ShapeConds.center_le (h : ShapeConds S A a t y n) (hn : 2 ≤ n) :
    ∃ ζ ∈ S, ∀ g ∈ S, (∀ s ∈ S, s * g = g * s) → g = 1 ∨ g = ζ := by
  obtain ⟨b, hD, hbo, hdis, hAmem, hAcomm⟩ := shape_core h
  obtain ⟨hAS, htS, hyS⟩ := ShapeConds.le_S h
  have haA : a ∈ A := (hAmem a).2 ⟨1, 0, by simp⟩
  have hbA : b ∈ A := (hAmem b).2 ⟨0, 1, by simp⟩
  have hh := h
  obtain ⟨hao, -, -, -, htt, hyy, -, -, -, -, -, hyA, -⟩ := h
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have ha1 : a ≠ 1 := fun h1 => shape_mul_self_ne_one hao hn (by rw [h1, mul_one])
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hζζ : (a * b) ^ 2 ^ k * (a * b) ^ 2 ^ k = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ', hD.ab.mul_pow, hD.a_pow, hD.b_pow, mul_one]
  refine ⟨(a * b) ^ 2 ^ k, hAS (pow_mem (mul_mem haA hbA) _), ?_⟩
  intro g hg hcent
  obtain ⟨x, hx, hxg⟩ := ShapeConds.decomp hh hg
  rcases hxg with rfl | rfl | rfl | rfl
  ·
    obtain ⟨i, j, rfl⟩ := (hAmem g).1 hx
    have ht : a ^ j * b ^ i = a ^ i * b ^ j := by
      have e : t * (a ^ i * b ^ j) * t⁻¹ = b ^ i * a ^ j := by
        calc t * (a ^ i * b ^ j) * t⁻¹ = (t * a ^ i * t⁻¹) * (t * b ^ j * t⁻¹) := by group
          _ = (t * a * t⁻¹) ^ i * (t * b * t⁻¹) ^ j := by rw [conj_zpow, conj_zpow]
          _ = b ^ i * a ^ j := by rw [hD.tab, hD.tba]
      have e2 : t * (a ^ i * b ^ j) * t⁻¹ = a ^ i * b ^ j := by
        rw [hcent t htS]; group
      calc a ^ j * b ^ i = b ^ i * a ^ j := (hD.ab.zpow_zpow j i).eq
        _ = a ^ i * b ^ j := by rw [← e, e2]
    obtain ⟨-, hij⟩ := shape_unique hdis ht
    have hy : (a ^ i * b ^ j) * (a ^ i * b ^ j) = 1 := by
      have h1 := hyA _ hx
      rw [hcent y hyS, mul_assoc, hyy, mul_one] at h1
      exact mul_eq_one_iff_eq_inv.2 h1
    rw [shape_AA hD.ab] at hy
    obtain ⟨c, hc⟩ := shape_half (by omega : 1 ≤ k + 1)
      ((shape_zpow_eq_one_iff hao _).1 (shape_prod hdis hy).1)
    have hgz : a ^ i * b ^ j = ((a * b) ^ 2 ^ k) ^ c := by
      have e1 : a ^ i * b ^ j = (a * b) ^ i := by rw [hD.ab.mul_zpow, hij]
      have e2 : (a * b) ^ i = ((a * b) ^ ((2 : ℤ) ^ k)) ^ c := by
        rw [hc, Nat.add_sub_cancel, zpow_mul]
      rw [e1, e2]
      congr 1
      rw [← zpow_natCast]
      push_cast
      rfl
    rcases zpow_eq_one_or_self hζζ c with h1 | h1
    · exact Or.inl (by rw [hgz, h1])
    · exact Or.inr (by rw [hgz, h1])
  ·
    exfalso
    have hc := hcent a (hAS haA)
    have h1 := shape_cancel_A (hAcomm x hx a haA) hc
    have hba : b = a := by
      calc b = t * a * t⁻¹ := hD.tab.symm
        _ = a * t * t⁻¹ := by rw [h1]
        _ = a := by group
    have h2 := hdis 1 1 (by rw [hba])
    rw [zpow_one] at h2
    exact ha1 h2
  ·
    exfalso
    have hc := hcent a (hAS haA)
    have h1 := shape_cancel_A (hAcomm x hx a haA) hc
    have h2 : a⁻¹ = a := by
      calc a⁻¹ = y * a * y⁻¹ := hD.ya.symm
        _ = a * y * y⁻¹ := by rw [h1]
        _ = a := by group
    exact shape_mul_self_ne_one hao hn (mul_eq_one_iff_eq_inv.2 h2.symm)
  ·
    exfalso
    have hc : a * (x * (t * y)) = x * (t * y) * a := by
      simpa only [mul_assoc] using hcent a (hAS haA)
    have h1 := shape_cancel_A (hAcomm x hx a haA) hc
    have h2 : t * a⁻¹ * t = a := by
      calc t * a⁻¹ * t = t * (y * a * y) * t := by rw [hyA a haA]
        _ = (t * y * a) * (y * t) := by group
        _ = a * (t * y) * (y * t) := by rw [h1]
        _ = a * (t * (y * y) * t) := by group
        _ = a := by rw [hyy, mul_one, htt, mul_one]
    have h3 : b⁻¹ = a := by
      calc b⁻¹ = (t * a * t⁻¹)⁻¹ := by rw [hD.tab]
        _ = t * a⁻¹ * t⁻¹ := by group
        _ = t * a⁻¹ * t := by rw [hti]
        _ = a := h2
    have h4 : a * b = 1 := mul_eq_one_iff_eq_inv.2 h3.symm
    have h5 := (shape_prod hdis (i := 1) (j := 1) (by simpa using h4)).1
    rw [zpow_one] at h5
    exact ha1 h5

end Shape

end CFSG.GH74.GLS.Stage1.Main
