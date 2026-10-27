module

public import CFSG.CGT.Foote81L6.Setup
public import CFSG.CGT.Foote81L6.Dihedral
public import CFSG.CharacterTheory.Semidihedral.NormalForm

public section

namespace CFSG.CGT.Foote81L6

open Subgroup DihedralGroup

section General

variable {G : Type*} [Group G]

theorem mem_sup_iff_of_le_normalizer {H K : Subgroup G} (hK : K ≤ normalizer (H : Set G))
    {g : G} : g ∈ H ⊔ K ↔ ∃ x ∈ H, ∃ y ∈ K, g = x * y := by
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left H K hK, Set.mem_mul]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩

theorem le_normalizer_of_comm {H K : Subgroup G} (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) :
    K ≤ normalizer (H : Set G) := by
  intro y hy
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have : y * h * y⁻¹ = h := by rw [← hc h hh y hy, mul_inv_cancel_right]
    rw [this]
    exact hh
  · intro hh
    have h2 := hc _ hh y hy
    have : h = y * h * y⁻¹ := by
      calc h = y⁻¹ * ((y * h * y⁻¹) * y) := by group
        _ = y⁻¹ * (y * (y * h * y⁻¹)) := by rw [h2]
        _ = y * h * y⁻¹ := by group
    rw [this]
    exact hh

theorem mem_normalizer_of_involution {H : Subgroup G} {g : G} (hg : g * g = 1)
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have := h _ hx
  have e : g * (g * x * g⁻¹) * g⁻¹ = x := by
    rw [hgi, ← mul_assoc, ← mul_assoc, hg, one_mul, mul_assoc, hg, mul_one]
  rwa [e] at this

theorem card_sup_of_le_normalizer {H K : Subgroup G} (hK : K ≤ normalizer (H : Set G))
    (hi : H ⊓ K = ⊥) : Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  let f : ↥H × ↥K → ↥(H ⊔ K) := fun p =>
    ⟨(p.1 : G) * p.2, mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
      have h1 : ((x : G) * y) = x' * y' := congrArg Subtype.val hxy
      have h2 : (x' : G)⁻¹ * x = y' * (y : G)⁻¹ := by
        calc (x' : G)⁻¹ * x = (x' : G)⁻¹ * (x * y) * (y : G)⁻¹ := by group
          _ = (x' : G)⁻¹ * (x' * y') * (y : G)⁻¹ := by rw [h1]
          _ = y' * (y : G)⁻¹ := by group
      have hmem : (x' : G)⁻¹ * x ∈ H ⊓ K :=
        mem_inf.2 ⟨mul_mem (inv_mem x'.2) x.2, h2 ▸ mul_mem y'.2 (inv_mem y.2)⟩
      rw [hi, mem_bot] at hmem
      have hx : (x : G) = x' := by
        rw [← mul_inv_cancel_left (x' : G) x, hmem, mul_one]
      have hy : (y : G) = y' := by
        rw [hx] at h1
        exact mul_left_cancel h1
      simp only [Prod.mk.injEq]
      exact ⟨Subtype.ext hx, Subtype.ext hy⟩
    · rintro ⟨g, hg⟩
      obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_iff_of_le_normalizer hK).1 hg
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  rw [← Nat.card_prod, Nat.card_congr (Equiv.ofBijective f hf)]

end General

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

theorem t_mul_t : D.t * D.t = 1 := by rw [← sq]; exact D.t_sq

theorem t_inv : D.t⁻¹ = D.t := inv_eq_of_mul_eq_one_right D.t_mul_t

theorem s_mul_s : D.s * D.s = 1 := by rw [← sq]; exact D.s_sq

theorem s_inv : D.s⁻¹ = D.s := inv_eq_of_mul_eq_one_right D.s_mul_s

include D in
theorem one_le_m : 1 ≤ m := by have := D.two_le_m; omega

include D in
theorem three_le_n : 3 ≤ n := by have := D.two_le_m; have := D.m_lt_n; omega

theorem a_mul_a : D.a * D.a = 1 := by
  rw [← sq, ← D.a_order]; exact pow_orderOf_eq_one _

theorem b₀_mul_b₀ : D.b₀ * D.b₀ = 1 := by
  rw [← sq, ← D.b₀_order]; exact pow_orderOf_eq_one _

theorem b₁_mul_b₁ : D.b₁ * D.b₁ = 1 := by
  rw [← sq, ← D.b₁_order]; exact pow_orderOf_eq_one _

theorem a_ne_one : D.a ≠ 1 := by
  intro h; have := D.a_order; rw [h, orderOf_one] at this; omega

theorem b₀_ne_one : D.b₀ ≠ 1 := by
  intro h; have := D.b₀_order; rw [h, orderOf_one] at this; omega

theorem b₁_ne_one : D.b₁ ≠ 1 := by
  intro h; have := D.b₁_order; rw [h, orderOf_one] at this; omega

theorem A_le_T : D.A ≤ T := (le_sup_left.trans le_sup_left).trans D.T_eq.symm.le

theorem B_le_T : D.B ≤ T := (le_sup_right.trans le_sup_left).trans D.T_eq.symm.le

theorem t_mem_T : D.t ∈ T := D.T_eq.symm.le (mem_sup_right (mem_zpowers _))

theorem T₀_le_T : D.T₀ ≤ T := sup_le D.A_le_T D.B_le_T

theorem B₀_le_B : D.B₀ ≤ D.B := by rw [D.B_eq]; exact le_sup_left.trans le_sup_left

theorem B₁_le_B : D.B₁ ≤ D.B := by rw [D.B_eq]; exact le_sup_right.trans le_sup_left

theorem B₀B₁_le_B : D.B₀ ⊔ D.B₁ ≤ D.B := sup_le D.B₀_le_B D.B₁_le_B

theorem s_mem_B : D.s ∈ D.B := by rw [D.B_eq]; exact mem_sup_right (mem_zpowers _)

theorem a_mem_T : D.a ∈ T := D.A_le_T D.a_mem

theorem b₀_mem_B : D.b₀ ∈ D.B := D.B₀_le_B D.b₀_mem

theorem b₁_mem_B : D.b₁ ∈ D.B := D.B₁_le_B D.b₁_mem

theorem b_mem_B₀B₁ : D.b ∈ D.B₀ ⊔ D.B₁ :=
  mul_mem (mem_sup_left D.b₀_mem) (mem_sup_right D.b₁_mem)

theorem b_mem_B : D.b ∈ D.B := D.B₀B₁_le_B D.b_mem_B₀B₁

theorem b_mem_T : D.b ∈ T := D.B_le_T D.b_mem_B

theorem card_A : Nat.card D.A = 2 ^ m := by
  obtain ⟨e⟩ := D.A_iso
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, ← pow_succ']
  congr 1
  have := D.one_le_m
  omega

theorem card_At : Nat.card ↥(D.A ⊔ zpowers D.t) = 2 ^ (m + 1) := by
  obtain ⟨e⟩ := D.At_iso
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, ← pow_succ']

theorem card_B₀ : Nat.card D.B₀ = 2 ^ n := by
  obtain ⟨e⟩ := D.B₀_iso
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, ← pow_succ']
  congr 1
  have := D.three_le_n
  omega

theorem card_B₁ : Nat.card D.B₁ = 2 ^ n := by
  obtain ⟨e⟩ := D.B₁_iso
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, ← pow_succ']
  congr 1
  have := D.three_le_n
  omega

theorem card_CBt : Nat.card ↥(D.B ⊓ centralizer ({D.t} : Set G)) = 2 ^ (n + 1) := by
  obtain ⟨e⟩ := D.CBt_iso
  rw [Nat.card_congr e.toEquiv, CFSG.Semidihedral.card _ (by have := D.three_le_n; omega)]

theorem finite_A : Finite D.A := Nat.finite_of_card_ne_zero (by rw [D.card_A]; positivity)

theorem finite_B₀ : Finite D.B₀ := Nat.finite_of_card_ne_zero (by rw [D.card_B₀]; positivity)

theorem finite_B₁ : Finite D.B₁ := Nat.finite_of_card_ne_zero (by rw [D.card_B₁]; positivity)

theorem eq_one_or_a_of_comm_At {x : G} (hx : x ∈ D.A ⊔ zpowers D.t)
    (hc : ∀ y ∈ D.A ⊔ zpowers D.t, y * x = x * y) : x = 1 ∨ x = D.a := by
  obtain ⟨e⟩ := D.At_iso
  have hcen : ∀ {u : G} (hu : u ∈ D.A ⊔ zpowers D.t),
      (∀ y ∈ D.A ⊔ zpowers D.t, y * u = u * y) → e ⟨u, hu⟩ = 1 ∨ e ⟨u, hu⟩ = zc m := by
    intro u hu huc
    refine eq_one_or_zc_of_comm D.two_le_m fun g => ?_
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (huc y y.2))
  have haA : D.a ∈ D.A ⊔ zpowers D.t := mem_sup_left D.a_mem
  have hea : e ⟨D.a, haA⟩ = zc m := by
    rcases hcen haA D.a_comm with h | h
    · exact absurd (congrArg Subtype.val (e.injective (h.trans e.map_one.symm))) D.a_ne_one
    · exact h
  rcases hcen hx hc with h | h
  · left
    exact congrArg Subtype.val (e.injective (h.trans e.map_one.symm))
  · right
    exact congrArg Subtype.val (e.injective (h.trans hea.symm))

theorem eq_one_or_b₀_of_comm {x : G} (hx : x ∈ D.B₀) (hc : ∀ y ∈ D.B₀, y * x = x * y) :
    x = 1 ∨ x = D.b₀ := by
  obtain ⟨e⟩ := D.B₀_iso
  have h2 : 2 ≤ n - 1 := by have := D.three_le_n; omega
  have hcen : ∀ {u : G} (hu : u ∈ D.B₀), (∀ y ∈ D.B₀, y * u = u * y) →
      e ⟨u, hu⟩ = 1 ∨ e ⟨u, hu⟩ = zc (n - 1) := by
    intro u hu huc
    refine eq_one_or_zc_of_comm h2 fun g => ?_
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (huc y y.2))
  have hb : e ⟨D.b₀, D.b₀_mem⟩ = zc (n - 1) := by
    rcases hcen D.b₀_mem D.b₀_comm with h | h
    · exact absurd (congrArg Subtype.val (e.injective (h.trans e.map_one.symm))) D.b₀_ne_one
    · exact h
  rcases hcen hx hc with h | h
  · exact Or.inl (congrArg Subtype.val (e.injective (h.trans e.map_one.symm)))
  · exact Or.inr (congrArg Subtype.val (e.injective (h.trans hb.symm)))

theorem eq_one_or_b₁_of_comm {x : G} (hx : x ∈ D.B₁) (hc : ∀ y ∈ D.B₁, y * x = x * y) :
    x = 1 ∨ x = D.b₁ := by
  obtain ⟨e⟩ := D.B₁_iso
  have h2 : 2 ≤ n - 1 := by have := D.three_le_n; omega
  have hcen : ∀ {u : G} (hu : u ∈ D.B₁), (∀ y ∈ D.B₁, y * u = u * y) →
      e ⟨u, hu⟩ = 1 ∨ e ⟨u, hu⟩ = zc (n - 1) := by
    intro u hu huc
    refine eq_one_or_zc_of_comm h2 fun g => ?_
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (huc y y.2))
  have hb : e ⟨D.b₁, D.b₁_mem⟩ = zc (n - 1) := by
    rcases hcen D.b₁_mem D.b₁_comm with h | h
    · exact absurd (congrArg Subtype.val (e.injective (h.trans e.map_one.symm))) D.b₁_ne_one
    · exact h
  rcases hcen hx hc with h | h
  · exact Or.inl (congrArg Subtype.val (e.injective (h.trans e.map_one.symm)))
  · exact Or.inr (congrArg Subtype.val (e.injective (h.trans hb.symm)))

theorem t_not_mem_A : D.t ∉ D.A := by
  intro ht
  have hle : D.A ⊔ zpowers D.t = D.A := sup_eq_left.2 (zpowers_le.2 ht)
  have h := D.card_At
  rw [hle, D.card_A] at h
  have : 2 ^ m < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self m)
  omega

theorem mem_T₀_iff {g : G} : g ∈ D.T₀ ↔ ∃ x ∈ D.A, ∃ y ∈ D.B, g = x * y :=
  mem_sup_iff_of_le_normalizer (le_normalizer_of_comm D.A_comm_B)

theorem t_not_mem_T₀ : D.t ∉ D.T₀ := by
  intro ht
  obtain ⟨x, hx, y, hy, hxy⟩ := D.mem_T₀_iff.1 ht
  have hyAt : y ∈ D.A ⊔ zpowers D.t := by
    have : y = x⁻¹ * D.t := by rw [hxy]; group
    rw [this]
    exact mul_mem (mem_sup_left (inv_mem hx)) (mem_sup_right (mem_zpowers _))
  have hcy : D.A ⊔ zpowers D.t ≤ centralizer ({y} : Set G) := by
    refine sup_le (fun u hu => ?_) (zpowers_le.2 ?_)
    · rw [mem_centralizer_singleton_iff]
      exact D.A_comm_B u hu y hy
    · rw [mem_centralizer_singleton_iff, hxy, mul_assoc, ← mul_assoc y, ← D.A_comm_B x hx y hy,
        mul_assoc]
  rcases D.eq_one_or_a_of_comm_At hyAt (fun u hu => mem_centralizer_singleton_iff.1 (hcy hu))
    with h1 | ha
  · rw [h1, mul_one] at hxy
    exact D.t_not_mem_A (hxy ▸ hx)
  · have : D.a ∈ D.A ⊓ D.B := ⟨D.a_mem, ha ▸ hy⟩
    rw [D.A_inf_B, mem_bot] at this
    exact D.a_ne_one this

theorem t_ne_one : D.t ≠ 1 := fun h => D.t_not_mem_T₀ (h ▸ one_mem _)

theorem orderOf_t : orderOf D.t = 2 := orderOf_eq_prime D.t_sq D.t_ne_one

private theorem zc_succ_eq (b : ℕ) : zc (b + 1) = r ((2 ^ b : ℕ) : ZMod (2 ^ (b + 1))) := by
  rw [← rho_pow (by omega : 1 ≤ b + 1), r_pow, one_mul, Nat.add_sub_cancel]

theorem At_iso_apply_a (e : ↥(D.A ⊔ zpowers D.t) ≃* DihedralGroup (2 ^ m)) :
    e ⟨D.a, mem_sup_left D.a_mem⟩ = zc m := by
  rcases eq_one_or_zc_of_comm D.two_le_m (c := e ⟨D.a, mem_sup_left D.a_mem⟩) (fun g => by
      obtain ⟨y, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext (D.a_comm y y.2))) with h | h
  · exact absurd (congrArg Subtype.val (e.injective (h.trans e.map_one.symm))) D.a_ne_one
  · exact h

theorem At_iso_apply_t (e : ↥(D.A ⊔ zpowers D.t) ≃* DihedralGroup (2 ^ m)) :
    ∃ j, e ⟨D.t, mem_sup_right (mem_zpowers _)⟩ = sr j := by
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by have := D.one_le_m; omega⟩
  have hea := D.At_iso_apply_a e
  rcases h : e ⟨D.t, mem_sup_right (mem_zpowers _)⟩ with i | j
  · exfalso
    have ht2 : (r i : DihedralGroup (2 ^ m)) * r i = 1 := by
      rw [← h, ← map_mul, ← e.map_one]
      exact congrArg e (Subtype.ext D.t_mul_t)
    rw [r_mul_r, ← r_zero] at ht2
    have hi : i + i = 0 := r.inj ht2
    subst hk
    rcases eq_zero_or_half hi with h0 | hh
    · apply D.t_ne_one
      have : e ⟨D.t, mem_sup_right (mem_zpowers _)⟩ = e 1 := by rw [h, h0, r_zero, e.map_one]
      exact congrArg Subtype.val (e.injective this)
    · apply D.t_not_mem_A
      have : e ⟨D.t, mem_sup_right (mem_zpowers _)⟩ = e ⟨D.a, mem_sup_left D.a_mem⟩ := by
        rw [h, hea, hh, zc_succ_eq]
      have := congrArg Subtype.val (e.injective this)
      simp only at this
      rw [this]
      exact D.a_mem
  · exact ⟨j, rfl⟩

theorem eq_one_or_a_of_comm_t {x : G} (hx : x ∈ D.A) (hxt : x * D.t = D.t * x) :
    x = 1 ∨ x = D.a := by
  obtain ⟨e⟩ := D.At_iso
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by have := D.one_le_m; omega⟩
  have htAt : D.t ∈ D.A ⊔ zpowers D.t := mem_sup_right (mem_zpowers _)
  have hxAt : x ∈ D.A ⊔ zpowers D.t := mem_sup_left hx
  have haAt : D.a ∈ D.A ⊔ zpowers D.t := mem_sup_left D.a_mem
  have hea : e ⟨D.a, haAt⟩ = zc m := D.At_iso_apply_a e
  obtain ⟨j, hj⟩ : ∃ j, e ⟨D.t, htAt⟩ = sr j := D.At_iso_apply_t e
  have hcomm : e ⟨x, hxAt⟩ * sr j = sr j * e ⟨x, hxAt⟩ := by
    rw [← hj, ← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext hxt)
  rcases hex : e ⟨x, hxAt⟩ with i | i
  · rw [hex, r_mul_sr, sr_mul_r] at hcomm
    have hi : i + i = 0 := by
      have := sr.inj hcomm
      linear_combination (-1 : ZMod (2 ^ m)) * this
    subst hk
    rcases eq_zero_or_half hi with h0 | hh
    · left
      have : e ⟨x, hxAt⟩ = e 1 := by rw [hex, h0, r_zero, e.map_one]
      exact congrArg Subtype.val (e.injective this)
    · right
      have : e ⟨x, hxAt⟩ = e ⟨D.a, haAt⟩ := by
        rw [hex, hea, hh, zc_succ_eq]
      exact congrArg Subtype.val (e.injective this)
  · exfalso
    rw [hex, sr_mul_sr, sr_mul_sr] at hcomm
    have hji : (j - i) + (j - i) = 0 := by
      have := r.inj hcomm
      linear_combination this
    subst hk
    have hxt' : x * D.t⁻¹ ∈ D.A ⊔ zpowers D.t :=
      mul_mem hxAt (inv_mem htAt)
    have hval : e ⟨x * D.t⁻¹, hxt'⟩ = r (j - i) := by
      have : (⟨x * D.t⁻¹, hxt'⟩ : ↥(D.A ⊔ zpowers D.t)) = ⟨x, hxAt⟩ * ⟨D.t, htAt⟩⁻¹ := rfl
      rw [this, map_mul, map_inv, hex, hj, inv_sr, sr_mul_sr]
    rcases eq_zero_or_half hji with h0 | hh
    · apply D.t_not_mem_A
      have : e ⟨x * D.t⁻¹, hxt'⟩ = e 1 := by rw [hval, h0, r_zero, e.map_one]
      have hx1 := congrArg Subtype.val (e.injective this)
      simp only [OneMemClass.coe_one] at hx1
      have : D.t = x := by
        have := congrArg (· * D.t) hx1
        simpa using this.symm
      rw [this]
      exact hx
    · apply D.t_not_mem_A
      have : e ⟨x * D.t⁻¹, hxt'⟩ = e ⟨D.a, haAt⟩ := by
        rw [hval, hea, hh, zc_succ_eq]
      have hx1 := congrArg Subtype.val (e.injective this)
      simp only at hx1
      have : D.t = D.a⁻¹ * x := by
        rw [← hx1]
        group
      rw [this]
      exact mul_mem (inv_mem D.a_mem) hx

theorem conj_s_mem_B₁ {x : G} (hx : x ∈ D.B₀) : D.s * x * D.s⁻¹ ∈ D.B₁ := by
  rw [← D.conj_s_B₀]
  exact ⟨x, hx, rfl⟩

theorem conj_s_mem_B₀ {y : G} (hy : y ∈ D.B₁) : D.s * y * D.s⁻¹ ∈ D.B₀ := by
  rw [← D.conj_s_B₀] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have e : D.s * ((MulAut.conj D.s).toMonoidHom x) * D.s⁻¹ = x := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [D.s_inv, ← mul_assoc, ← mul_assoc, D.s_mul_s, one_mul, mul_assoc, D.s_mul_s, mul_one]
  rw [e]
  exact hx

theorem mem_B₀B₁_iff {g : G} : g ∈ D.B₀ ⊔ D.B₁ ↔ ∃ x ∈ D.B₀, ∃ y ∈ D.B₁, g = x * y :=
  mem_sup_iff_of_le_normalizer (le_normalizer_of_comm D.B₀_comm_B₁)

theorem s_mem_normalizer_B₀B₁ : D.s ∈ normalizer ((D.B₀ ⊔ D.B₁ : Subgroup G) : Set G) := by
  refine mem_normalizer_of_involution D.s_mul_s fun g hg => ?_
  obtain ⟨x, hx, y, hy, rfl⟩ := D.mem_B₀B₁_iff.1 hg
  have e : D.s * (x * y) * D.s⁻¹ = (D.s * x * D.s⁻¹) * (D.s * y * D.s⁻¹) := by group
  rw [e]
  exact mul_mem (mem_sup_right (D.conj_s_mem_B₁ hx)) (mem_sup_left (D.conj_s_mem_B₀ hy))

theorem conj_s_b₀ : D.s * D.b₀ * D.s⁻¹ = D.b₁ := by
  have hmem := D.conj_s_mem_B₁ D.b₀_mem
  rcases D.eq_one_or_b₁_of_comm hmem (fun y hy => by
      have hy' := D.conj_s_mem_B₀ hy
      have hc := D.b₀_comm _ hy'
      have e1 : y = D.s * (D.s * y * D.s⁻¹) * D.s⁻¹ := by
        rw [D.s_inv]
        calc y = (D.s * D.s) * y * (D.s * D.s) := by rw [D.s_mul_s, one_mul, mul_one]
          _ = D.s * (D.s * y * D.s) * D.s := by group
      calc y * (D.s * D.b₀ * D.s⁻¹)
          = D.s * ((D.s * y * D.s⁻¹) * D.b₀) * D.s⁻¹ := by
            conv_lhs => rw [e1]
            group
        _ = D.s * (D.b₀ * (D.s * y * D.s⁻¹)) * D.s⁻¹ := by rw [hc]
        _ = (D.s * D.b₀ * D.s⁻¹) * y := by
            conv_rhs => rw [e1]
            group) with h | h
  · exfalso
    apply D.b₀_ne_one
    have : D.b₀ = D.s⁻¹ * (D.s * D.b₀ * D.s⁻¹) * D.s := by group
    rw [this, h]
    group
  · exact h

theorem conj_s_b₁ : D.s * D.b₁ * D.s⁻¹ = D.b₀ := by
  rw [← D.conj_s_b₀, D.s_inv, ← mul_assoc, ← mul_assoc, D.s_mul_s, one_mul, mul_assoc, D.s_mul_s,
    mul_one]

theorem s_not_mem_B₀B₁ : D.s ∉ D.B₀ ⊔ D.B₁ := by
  intro hs
  obtain ⟨x, hx, y, hy, hxy⟩ := D.mem_B₀B₁_iff.1 hs
  have h1 : D.s * D.b₀ * D.s⁻¹ = D.b₀ := by
    rw [hxy, mul_inv_rev]
    have hyb : y * D.b₀ = D.b₀ * y := (D.B₀_comm_B₁ D.b₀ D.b₀_mem y hy).symm
    have hxb : x * D.b₀ = D.b₀ * x := D.b₀_comm x hx
    calc x * y * D.b₀ * (y⁻¹ * x⁻¹) = x * (y * D.b₀) * y⁻¹ * x⁻¹ := by group
      _ = x * D.b₀ * x⁻¹ := by rw [hyb]; group
      _ = D.b₀ := by rw [hxb]; group
  rw [D.conj_s_b₀] at h1
  have : D.b₀ ∈ D.B₀ ⊓ D.B₁ := ⟨D.b₀_mem, h1 ▸ D.b₁_mem⟩
  rw [D.B₀_inf_B₁, mem_bot] at this
  exact D.b₀_ne_one this

theorem s_ne_one : D.s ≠ 1 := fun h => D.s_not_mem_B₀B₁ (h ▸ one_mem _)

theorem orderOf_s : orderOf D.s = 2 := orderOf_eq_prime D.s_sq D.s_ne_one

theorem mem_B_iff {g : G} : g ∈ D.B ↔ g ∈ D.B₀ ⊔ D.B₁ ∨ g * D.s ∈ D.B₀ ⊔ D.B₁ := by
  have hle : zpowers D.s ≤ normalizer ((D.B₀ ⊔ D.B₁ : Subgroup G) : Set G) :=
    zpowers_le.2 D.s_mem_normalizer_B₀B₁
  rw [D.B_eq, mem_sup_iff_of_le_normalizer hle]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    have hy2 : y = 1 ∨ y = D.s := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
      rw [zpow_eq_zpow_emod' k D.s_sq]
      rcases Int.emod_two_eq_zero_or_one k with h0 | h1
      · left; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h0, zpow_zero]
      · right; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h1, zpow_one]
    rcases hy2 with rfl | rfl
    · left; rwa [mul_one]
    · right; rwa [mul_assoc, D.s_mul_s, mul_one]
  · rintro (h | h)
    · exact ⟨g, h, 1, one_mem _, (mul_one g).symm⟩
    · refine ⟨g * D.s, h, D.s, mem_zpowers _, ?_⟩
      rw [mul_assoc, D.s_mul_s, mul_one]

theorem card_B₀B₁ : Nat.card ↥(D.B₀ ⊔ D.B₁) = 2 ^ (2 * n) := by
  rw [card_sup_of_le_normalizer (le_normalizer_of_comm D.B₀_comm_B₁) D.B₀_inf_B₁, D.card_B₀,
    D.card_B₁, ← pow_add, two_mul]

theorem card_B : Nat.card D.B = 2 ^ (2 * n + 1) := by
  have hle : zpowers D.s ≤ normalizer ((D.B₀ ⊔ D.B₁ : Subgroup G) : Set G) :=
    zpowers_le.2 D.s_mem_normalizer_B₀B₁
  have hinf : (D.B₀ ⊔ D.B₁) ⊓ zpowers D.s = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hg, hgs⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hgs
    rw [mem_bot, zpow_eq_zpow_emod' k D.s_sq]
    rw [zpow_eq_zpow_emod' k D.s_sq] at hg
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h0, zpow_zero]
    · rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h1, zpow_one] at hg
      exact absurd hg D.s_not_mem_B₀B₁
  rw [D.B_eq, card_sup_of_le_normalizer hle hinf, D.card_B₀B₁, Nat.card_zpowers, D.orderOf_s,
    pow_succ]

theorem t_mem_normalizer_A : D.t ∈ normalizer (D.A : Set G) :=
  mem_normalizer_of_involution D.t_mul_t D.conj_t_A

theorem t_mem_normalizer_B : D.t ∈ normalizer (D.B : Set G) :=
  mem_normalizer_of_involution D.t_mul_t D.conj_t_B

theorem T_le_normalizer_A : T ≤ normalizer (D.A : Set G) :=
  D.T_eq.le.trans <| sup_le (sup_le le_normalizer (le_normalizer_of_comm D.A_comm_B))
    (zpowers_le.2 D.t_mem_normalizer_A)

theorem T_le_normalizer_B : T ≤ normalizer (D.B : Set G) :=
  D.T_eq.le.trans <| sup_le
    (sup_le (le_normalizer_of_comm fun x hx y hy => (D.A_comm_B y hy x hx).symm) le_normalizer)
    (zpowers_le.2 D.t_mem_normalizer_B)

theorem T_le_normalizer_T₀ : T ≤ normalizer (D.T₀ : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  have hA := mem_normalizer_iff.1 (D.T_le_normalizer_A hg)
  have hB := mem_normalizer_iff.1 (D.T_le_normalizer_B hg)
  constructor
  · intro hx
    obtain ⟨u, hu, v, hv, rfl⟩ := D.mem_T₀_iff.1 hx
    have e : g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) := by group
    rw [e]
    exact mul_mem (mem_sup_left ((hA u).1 hu)) (mem_sup_right ((hB v).1 hv))
  · intro hx
    obtain ⟨u, hu, v, hv, huv⟩ := D.mem_T₀_iff.1 hx
    have e : x = (g⁻¹ * u * g) * (g⁻¹ * v * g) := by
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = (g⁻¹ * u * g) * (g⁻¹ * v * g) := by rw [huv]; group
    have hu' : g⁻¹ * u * g ∈ D.A := by
      have := (hA (g⁻¹ * u * g)).2
      rw [show g * (g⁻¹ * u * g) * g⁻¹ = u by group] at this
      exact this hu
    have hv' : g⁻¹ * v * g ∈ D.B := by
      have := (hB (g⁻¹ * v * g)).2
      rw [show g * (g⁻¹ * v * g) * g⁻¹ = v by group] at this
      exact this hv
    rw [e]
    exact mul_mem (mem_sup_left hu') (mem_sup_right hv')

theorem mem_At_iff {g : G} : g ∈ D.A ⊔ zpowers D.t ↔ g ∈ D.A ∨ g * D.t ∈ D.A := by
  have hle : zpowers D.t ≤ normalizer (D.A : Set G) := zpowers_le.2 D.t_mem_normalizer_A
  rw [mem_sup_iff_of_le_normalizer hle]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    rw [zpow_eq_zpow_emod' k D.t_sq]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left; rwa [show ((2 : ℕ) : ℤ) = 2 from rfl, h0, zpow_zero, mul_one]
    · right; rwa [show ((2 : ℕ) : ℤ) = 2 from rfl, h1, zpow_one, mul_assoc, D.t_mul_t, mul_one]
  · rintro (h | h)
    · exact ⟨g, h, 1, one_mem _, (mul_one g).symm⟩
    · refine ⟨g * D.t, h, D.t, mem_zpowers _, ?_⟩
      rw [mul_assoc, D.t_mul_t, mul_one]

theorem mul_self_mem_A_of_mem_At {g : G} (hg : g ∈ D.A ⊔ zpowers D.t) : g * g ∈ D.A := by
  rcases D.mem_At_iff.1 hg with h | h
  · exact mul_mem h h
  · have e : g * g = (g * D.t) * (D.t * (g * D.t) * D.t⁻¹) := by
      rw [D.t_inv]
      calc g * g = g * (D.t * D.t) * g * (D.t * D.t) := by rw [D.t_mul_t, mul_one, mul_one]
        _ = (g * D.t) * (D.t * (g * D.t) * D.t) := by group
    rw [e]
    exact mul_mem h (D.conj_t_A _ h)

theorem mem_T_iff {g : G} : g ∈ T ↔ g ∈ D.T₀ ∨ g * D.t ∈ D.T₀ := by
  have hle : zpowers D.t ≤ normalizer (D.T₀ : Set G) :=
    zpowers_le.2 (D.T_le_normalizer_T₀ D.t_mem_T)
  have hT : g ∈ T ↔ g ∈ D.T₀ ⊔ zpowers D.t := ⟨fun h => D.T_eq.le h, fun h => D.T_eq.symm.le h⟩
  rw [hT, mem_sup_iff_of_le_normalizer hle]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    rw [zpow_eq_zpow_emod' k D.t_sq]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left; rwa [show ((2 : ℕ) : ℤ) = 2 from rfl, h0, zpow_zero, mul_one]
    · right; rwa [show ((2 : ℕ) : ℤ) = 2 from rfl, h1, zpow_one, mul_assoc, D.t_mul_t, mul_one]
  · rintro (h | h)
    · exact ⟨g, h, 1, one_mem _, (mul_one g).symm⟩
    · refine ⟨g * D.t, h, D.t, mem_zpowers _, ?_⟩
      rw [mul_assoc, D.t_mul_t, mul_one]

theorem card_T₀ : Nat.card D.T₀ = 2 ^ (m + 2 * n + 1) := by
  rw [FooteCore.T₀, card_sup_of_le_normalizer (le_normalizer_of_comm D.A_comm_B) D.A_inf_B,
    D.card_A, D.card_B, ← pow_add, add_assoc]

include D in
theorem card_T : Nat.card T = 2 ^ (m + 2 * n + 2) := by
  have hle : zpowers D.t ≤ normalizer (D.T₀ : Set G) :=
    zpowers_le.2 (D.T_le_normalizer_T₀ D.t_mem_T)
  have hinf : D.T₀ ⊓ zpowers D.t = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hg, hgt⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hgt
    rw [mem_bot, zpow_eq_zpow_emod' k D.t_sq]
    rw [zpow_eq_zpow_emod' k D.t_sq] at hg
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h0, zpow_zero]
    · rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h1, zpow_one] at hg
      exact absurd hg D.t_not_mem_T₀
  have hT : Nat.card T = Nat.card ↥(D.T₀ ⊔ zpowers D.t) :=
    congrArg (fun X : Subgroup G => Nat.card ↥X) D.T_eq
  rw [hT, card_sup_of_le_normalizer hle hinf, D.card_T₀, Nat.card_zpowers, D.orderOf_t]
  ring

include D in
theorem isPGroup_T : IsPGroup 2 T := IsPGroup.of_card D.card_T

include D in
theorem finite_T : Finite T := Nat.finite_of_card_ne_zero (by rw [D.card_T]; positivity)

theorem a_comm_T {x : G} (hx : x ∈ T) : x * D.a = D.a * x := by
  have hle : T ≤ centralizer ({D.a} : Set G) := by
    refine D.T_eq.le.trans (sup_le (sup_le (fun u hu => ?_) (fun u hu => ?_)) (zpowers_le.2 ?_))
    · exact mem_centralizer_singleton_iff.2 (D.a_comm u (mem_sup_left hu))
    · exact mem_centralizer_singleton_iff.2 (D.A_comm_B D.a D.a_mem u hu).symm
    · exact mem_centralizer_singleton_iff.2 (D.a_comm D.t (mem_sup_right (mem_zpowers _)))
  exact mem_centralizer_singleton_iff.1 (hle hx)

theorem b_comm_B {x : G} (hx : x ∈ D.B) : x * D.b = D.b * x := by
  have hle : D.B ≤ centralizer ({D.b} : Set G) := by
    rw [D.B_eq]
    refine sup_le (sup_le (fun u hu => ?_) (fun u hu => ?_)) (zpowers_le.2 ?_)
    · rw [mem_centralizer_singleton_iff, FooteCore.b]
      symm
      have h1 := D.b₀_comm u hu
      have h2 := D.B₀_comm_B₁ u hu D.b₁ D.b₁_mem
      calc D.b₀ * D.b₁ * u = D.b₀ * (D.b₁ * u) := mul_assoc _ _ _
        _ = D.b₀ * (u * D.b₁) := by rw [h2]
        _ = (D.b₀ * u) * D.b₁ := (mul_assoc _ _ _).symm
        _ = (u * D.b₀) * D.b₁ := by rw [h1]
        _ = u * (D.b₀ * D.b₁) := mul_assoc _ _ _
    · rw [mem_centralizer_singleton_iff, FooteCore.b]
      symm
      have h1 := D.b₁_comm u hu
      have h2 := D.B₀_comm_B₁ D.b₀ D.b₀_mem u hu
      calc D.b₀ * D.b₁ * u = D.b₀ * (u * D.b₁) := by rw [mul_assoc, ← h1]
        _ = (D.b₀ * u) * D.b₁ := (mul_assoc _ _ _).symm
        _ = (u * D.b₀) * D.b₁ := by rw [h2]
        _ = u * (D.b₀ * D.b₁) := mul_assoc _ _ _
    · rw [mem_centralizer_singleton_iff, FooteCore.b]
      symm
      have h1 : D.s * (D.b₀ * D.b₁) * D.s⁻¹ = D.b₁ * D.b₀ := by
        rw [show D.s * (D.b₀ * D.b₁) * D.s⁻¹ = (D.s * D.b₀ * D.s⁻¹) * (D.s * D.b₁ * D.s⁻¹) by group,
          D.conj_s_b₀, D.conj_s_b₁]
      have h2 : D.b₁ * D.b₀ = D.b₀ * D.b₁ := (D.B₀_comm_B₁ D.b₀ D.b₀_mem D.b₁ D.b₁_mem).symm
      calc D.b₀ * D.b₁ * D.s = D.s * (D.s * (D.b₀ * D.b₁) * D.s⁻¹) := by
            rw [D.s_inv]
            calc D.b₀ * D.b₁ * D.s = (D.s * D.s) * (D.b₀ * D.b₁) * D.s := by
                  rw [D.s_mul_s, one_mul]
              _ = D.s * (D.s * (D.b₀ * D.b₁) * D.s) := by group
        _ = D.s * (D.b₀ * D.b₁) := by rw [h1, h2]
  exact mem_centralizer_singleton_iff.1 (hle hx)

theorem eq_one_or_b_of_comm_B {x : G} (hx : x ∈ D.B) (hc : ∀ y ∈ D.B, y * x = x * y) :
    x = 1 ∨ x = D.b := by
  rcases D.mem_B_iff.1 hx with h | h
  · obtain ⟨u, hu, v, hv, rfl⟩ := D.mem_B₀B₁_iff.1 h
    have hu' : ∀ y ∈ D.B₀, y * u = u * y := by
      intro y hy
      have h1 := hc y (D.B₀_le_B hy)
      have h2 : y * v = v * y := D.B₀_comm_B₁ y hy v hv
      have : y * u * v = u * y * v := by
        calc y * u * v = y * (u * v) := mul_assoc _ _ _
          _ = u * v * y := h1
          _ = u * (v * y) := mul_assoc _ _ _
          _ = u * (y * v) := by rw [h2]
          _ = u * y * v := (mul_assoc _ _ _).symm
      exact mul_right_cancel this
    have hv' : ∀ y ∈ D.B₁, y * v = v * y := by
      intro y hy
      have h1 := hc y (D.B₁_le_B hy)
      have h2 : u * y = y * u := D.B₀_comm_B₁ u hu y hy
      have : u * (y * v) = u * (v * y) := by
        calc u * (y * v) = (u * y) * v := (mul_assoc _ _ _).symm
          _ = (y * u) * v := by rw [h2]
          _ = y * (u * v) := mul_assoc _ _ _
          _ = u * v * y := h1
          _ = u * (v * y) := mul_assoc _ _ _
      exact mul_left_cancel this
    have hs := hc D.s D.s_mem_B
    have hconj : D.s * (u * v) * D.s⁻¹ = u * v := by
      rw [hs, mul_inv_cancel_right]
    rcases D.eq_one_or_b₀_of_comm hu hu' with rfl | rfl <;>
      rcases D.eq_one_or_b₁_of_comm hv hv' with rfl | rfl
    · left; exact mul_one 1
    · exfalso
      rw [one_mul, D.conj_s_b₁] at hconj
      have : D.b₀ ∈ D.B₀ ⊓ D.B₁ := ⟨D.b₀_mem, hconj ▸ D.b₁_mem⟩
      rw [D.B₀_inf_B₁, mem_bot] at this
      exact D.b₀_ne_one this
    · exfalso
      rw [mul_one, D.conj_s_b₀] at hconj
      have : D.b₁ ∈ D.B₀ ⊓ D.B₁ := ⟨hconj ▸ D.b₀_mem, D.b₁_mem⟩
      rw [D.B₀_inf_B₁, mem_bot] at this
      exact D.b₁_ne_one this
    · right; rfl
  · exfalso
    obtain ⟨u, hu, v, hv, huv⟩ := D.mem_B₀B₁_iff.1 h
    have hx' : x = u * v * D.s := by rw [← huv, mul_assoc, D.s_mul_s, mul_one]
    have hcb := hc D.b₀ D.b₀_mem_B
    have h1 : x * D.b₀ * x⁻¹ = D.b₁ := by
      rw [hx', mul_inv_rev, mul_inv_rev]
      have hvb : v * D.b₁ = D.b₁ * v := D.b₁_comm v hv
      have hub : u * D.b₁ = D.b₁ * u := D.B₀_comm_B₁ u hu D.b₁ D.b₁_mem
      calc u * v * D.s * D.b₀ * (D.s⁻¹ * (v⁻¹ * u⁻¹))
          = u * v * (D.s * D.b₀ * D.s⁻¹) * v⁻¹ * u⁻¹ := by group
        _ = u * (v * D.b₁) * v⁻¹ * u⁻¹ := by rw [D.conj_s_b₀]; group
        _ = (u * D.b₁) * u⁻¹ := by rw [hvb]; group
        _ = D.b₁ := by rw [hub]; group
    have h2 : x * D.b₀ * x⁻¹ = D.b₀ := by rw [← hcb, mul_inv_cancel_right]
    rw [h1] at h2
    have : D.b₁ ∈ D.B₀ ⊓ D.B₁ := ⟨h2 ▸ D.b₀_mem, D.b₁_mem⟩
    rw [D.B₀_inf_B₁, mem_bot] at this
    exact D.b₁_ne_one this

theorem b_ne_one : D.b ≠ 1 := by
  intro h
  have h1 : D.b₀ = D.b₁⁻¹ := eq_inv_of_mul_eq_one_left h
  have : D.b₀ ∈ D.B₀ ⊓ D.B₁ := mem_inf.2 ⟨D.b₀_mem, h1 ▸ inv_mem D.b₁_mem⟩
  rw [D.B₀_inf_B₁, mem_bot] at this
  exact D.b₀_ne_one this

theorem b_mul_b : D.b * D.b = 1 := by
  rw [FooteCore.b]
  have h2 : D.b₁ * D.b₀ = D.b₀ * D.b₁ := (D.B₀_comm_B₁ D.b₀ D.b₀_mem D.b₁ D.b₁_mem).symm
  calc D.b₀ * D.b₁ * (D.b₀ * D.b₁) = D.b₀ * (D.b₁ * D.b₀) * D.b₁ := by group
    _ = D.b₀ * (D.b₀ * D.b₁) * D.b₁ := by rw [h2]
    _ = (D.b₀ * D.b₀) * (D.b₁ * D.b₁) := by group
    _ = 1 := by rw [D.b₀_mul_b₀, D.b₁_mul_b₁, one_mul]

theorem b_comm_T {x : G} (hx : x ∈ T) : x * D.b = D.b * x := by
  have htb : D.t * D.b * D.t⁻¹ = D.b := by
    have hmem : D.t * D.b * D.t⁻¹ ∈ D.B := D.conj_t_B _ D.b_mem_B
    rcases D.eq_one_or_b_of_comm_B hmem (fun y hy => by
        have hy' : D.t⁻¹ * y * D.t ∈ D.B := by
          rw [D.t_inv]
          have := D.conj_t_B y hy
          rwa [D.t_inv] at this
        have hc := D.b_comm_B hy'
        calc y * (D.t * D.b * D.t⁻¹) = D.t * ((D.t⁻¹ * y * D.t) * D.b) * D.t⁻¹ := by group
          _ = D.t * (D.b * (D.t⁻¹ * y * D.t)) * D.t⁻¹ := by rw [hc]
          _ = (D.t * D.b * D.t⁻¹) * y := by group) with h | h
    · exfalso
      apply D.b_ne_one
      have : D.b = D.t⁻¹ * (D.t * D.b * D.t⁻¹) * D.t := by group
      rw [this, h]
      group
    · exact h
  have hle : T ≤ centralizer ({D.b} : Set G) := by
    refine D.T_eq.le.trans (sup_le (sup_le (fun u hu => ?_) (fun u hu => ?_)) (zpowers_le.2 ?_))
    · exact mem_centralizer_singleton_iff.2 (D.A_comm_B u hu D.b D.b_mem_B)
    · exact mem_centralizer_singleton_iff.2 (D.b_comm_B hu)
    · rw [mem_centralizer_singleton_iff]
      symm
      calc D.b * D.t = (D.t * D.b * D.t⁻¹) * D.t := by rw [htb]
        _ = D.t * D.b := by group
  exact mem_centralizer_singleton_iff.1 (hle hx)

end FooteCore

end CFSG.CGT.Foote81L6
