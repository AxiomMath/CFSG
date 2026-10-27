module

public import CFSG.ClassicalInvolution.Asc77.AscT7U5
public import CFSG.ClassicalInvolution.Asc77.AscT7U6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

section Calculus

variable {G : Type} [Group G] {R : Subgroup G} {x y : G}

theorem zpow_eq_one_iff_eight (c : T7F2.QuatCoord R x y 2) {e : ℤ} : x ^ e = 1 ↔ (8 : ℤ) ∣ e := by
  have h := c.zpow_eq_iff (i := e) (j := 0)
  rw [zpow_zero, sub_zero] at h
  norm_num at h
  exact h

theorem zpow_eq_zpow_iff_eight (c : T7F2.QuatCoord R x y 2) {e f : ℤ} :
    x ^ e = x ^ f ↔ (8 : ℤ) ∣ e - f := by
  have h := c.zpow_eq_iff (i := e) (j := f)
  norm_num at h
  exact h

theorem xa_mul_x (e f : ℤ) : (y * x ^ e) * x ^ f = y * x ^ (e + f) := by
  rw [mul_assoc, ← zpow_add]

theorem x_mul_xa (c : T7F2.QuatCoord R x y 2) (e f : ℤ) :
    x ^ e * (y * x ^ f) = y * x ^ (f - e) := by
  rw [← mul_assoc, c.zpow_a_mul_b, mul_assoc, ← zpow_add]
  congr 2
  ring

theorem xa_mul_xa (c : T7F2.QuatCoord R x y 2) (e f : ℤ) :
    (y * x ^ e) * (y * x ^ f) = x ^ (4 - e + f) := by
  have h := c.mul_xa_xa e f
  norm_num at h
  exact h

theorem inv_xa (c : T7F2.QuatCoord R x y 2) (e : ℤ) : (y * x ^ e)⁻¹ = y * x ^ (e - 4) := by
  apply inv_eq_of_mul_eq_one_right
  rw [xa_mul_xa c]
  simp

theorem conj_xa_x (c : T7F2.QuatCoord R x y 2) (m : ℤ) :
    (y * x ^ m) * x * (y * x ^ m)⁻¹ = x ^ (-1 : ℤ) := by
  rw [inv_xa c]
  have h1 : (y * x ^ m) * x = y * x ^ (m + 1) := by
    have := xa_mul_x (x := x) (y := y) m 1
    rwa [zpow_one] at this
  rw [h1, xa_mul_xa c]
  congr 1
  ring

theorem conj_xa_y (c : T7F2.QuatCoord R x y 2) (m : ℤ) :
    (y * x ^ m) * y * (y * x ^ m)⁻¹ = y * x ^ (2 * m) := by
  rw [inv_xa c]
  have h1 : (y * x ^ m) * y = x ^ (4 - m) := by
    have := xa_mul_xa c m 0
    rwa [zpow_zero, mul_one, add_zero] at this
  rw [h1, x_mul_xa c]
  congr 1
  rw [zpow_eq_zpow_iff_eight c]
  exact ⟨-1, by ring⟩

end Calculus

section Classify

variable {G : Type} [Group G] [Finite G] {R V : Subgroup G} {z : G}

theorem aux_mul (i j r : ℤ) (hi : i % 8 = r) : ∃ w : ℤ, i * j = r * j + 8 * w := by
  refine ⟨(i / 8) * j, ?_⟩
  have h : i = 8 * (i / 8) + r := by omega
  calc i * j = (8 * (i / 8) + r) * j := by rw [← h]
    _ = r * j + 8 * ((i / 8) * j) := by ring

theorem exists_inner_of_mem_sup {m : G} (hm : m ∈ R ⊔ (V ⊓ Subgroup.centralizer (R : Set G))) :
    ∃ r ∈ R, ∀ w ∈ R, (r⁻¹ * m) * w = w * (r⁻¹ * m) := by
  obtain ⟨ρ, hρ, c, hc, rfl⟩ := T7F2.Out.exists_mul_of_mem_sup_of_commute
    (fun a (ha : a ∈ R) b (hb : b ∈ V ⊓ Subgroup.centralizer (R : Set G)) =>
      Subgroup.mem_centralizer_iff.mp hb.2 a ha) hm
  refine ⟨ρ, hρ, fun w hw => ?_⟩
  have h1 : (ρ⁻¹ * (ρ * c)) = c := by group
  rw [h1]
  exact (Subgroup.mem_centralizer_iff.mp hc.2 w hw).symm

theorem mix_of_card_ge_four (hR : IsQuatSub R) (hz : IsUniqueInvolution R z)
    (hR16 : Nat.card R = 16) (hRV : R ≤ V) (hV2 : IsPGroup 2 ↥V)
    (hVR : ∀ y ∈ V, conjSub y R = R) {a : G} (haV : a ∈ V) (ha2 : a * a = 1)
    (hfix : 4 ≤ Nat.card ↥(R ⊓ Subgroup.centralizer ({a} : Set G))) :
    (∃ r ∈ R, ∀ w ∈ R, (r⁻¹ * a) * w = w * (r⁻¹ * a)) ∨
      ∃ r ∈ R, (a * r) * (a * r) = 1 ∧ IsFAut R (a * r) := by
  obtain ⟨x, y, n, c, hinv⟩ := T7F2.exists_coord hR hz hV2 hVR
  have s : T7F2.Out.Setting R V x y n := ⟨c, hRV, hVR, hinv⟩
  have hn : n = 2 := by
    have h1 := c.natCard
    rw [hR16] at h1
    have h2 : (2 : ℕ) ^ (n + 2) = 2 ^ 4 := by rw [← h1]; norm_num
    have := Nat.pow_right_injective (le_refl 2) h2
    omega
  subst hn
  obtain ⟨i, j, hi, hax, hay⟩ := s.coord_of_mem haV
  have hzx : z = x ^ (4 : ℤ) := by
    have := T7U.z_eq_pow_of_coord c hz
    rw [this]
    norm_num
  have hja : (8 : ℤ) ∣ j + i * j := by
    have h1 := T7F2.Out.coord_mul_b hax hay hay
    rw [ha2, inv_one, one_mul, mul_one] at h1
    have h2 : y * x ^ (j + i * j) = y * 1 := by rw [mul_one]; exact h1.symm
    exact (zpow_eq_one_iff_eight c).mp (mul_left_cancel h2)
  have hi8 : i % 8 = 1 ∨ i % 8 = 3 ∨ i % 8 = 5 ∨ i % 8 = 7 := by
    obtain ⟨t, rfl⟩ := hi
    omega
  have hxi : ∀ e : ℤ, a * x ^ e * a⁻¹ = x ^ (i * e) := fun e => T7F2.Out.conj_zpow_a hax e
  have hconj_xa : ∀ e : ℤ, a * (y * x ^ e) * a⁻¹ = y * x ^ (j + i * e) := by
    intro e
    calc a * (y * x ^ e) * a⁻¹ = (a * y * a⁻¹) * (a * x ^ e * a⁻¹) := by group
      _ = (y * x ^ j) * x ^ (i * e) := by rw [hay, hxi]
      _ = y * x ^ (j + i * e) := xa_mul_x j (i * e)
  rcases hi8 with h1 | h3 | h5 | h7
  ·
    obtain ⟨w, hw⟩ := aux_mul i j 1 h1
    have hjev : Even j := ⟨j / 2, by omega⟩
    have hcong : x ^ i = x ∨ x ^ i = x⁻¹ := by
      left
      have := (zpow_eq_zpow_iff_eight c (e := i) (f := 1)).mpr ⟨(i - 1) / 8, by omega⟩
      simpa using this
    exact Or.inl (exists_inner_of_mem_sup (T7F2.Out.mem_sup_of_cong s haV hi hjev hax hay hcong))
  ·
    obtain ⟨w, hw⟩ := aux_mul i j 3 h3
    rw [hw] at hja
    obtain ⟨j₁, hj₁⟩ : ∃ j₁ : ℤ, j = 2 * j₁ := ⟨j / 2, by omega⟩
    subst hj₁
    have hrR : y * x ^ (2 - j₁) ∈ R := R.mul_mem c.hb (R.zpow_mem c.ha _)
    refine Or.inr ⟨y * x ^ (2 - j₁), hrR, ?_, ?_⟩
    ·
      obtain ⟨w₁, hw₁⟩ := aux_mul i (2 - j₁) 3 h3
      have e1 : (a * (y * x ^ (2 - j₁))) * (a * (y * x ^ (2 - j₁))) =
          (a * (y * x ^ (2 - j₁)) * a⁻¹) * (a * a) * (y * x ^ (2 - j₁)) := by group
      rw [e1, ha2, mul_one, hconj_xa, xa_mul_xa c, zpow_eq_one_iff_eight c]
      omega
    · have hbV : a * (y * x ^ (2 - j₁)) ∈ V := V.mul_mem haV (hRV hrR)
      have hx : (a * (y * x ^ (2 - j₁))) * x * (a * (y * x ^ (2 - j₁)))⁻¹ =
          x ^ ((1 : ℤ) + 2 ^ (0 + 2)) := by
        have e2 : (a * (y * x ^ (2 - j₁))) * x * (a * (y * x ^ (2 - j₁)))⁻¹ =
            a * ((y * x ^ (2 - j₁)) * x * (y * x ^ (2 - j₁))⁻¹) * a⁻¹ := by group
        rw [e2, conj_xa_x c, hxi, zpow_eq_zpow_iff_eight c]
        norm_num
        omega
      have hy : (a * (y * x ^ (2 - j₁))) * y * (a * (y * x ^ (2 - j₁)))⁻¹ = y ∨
          (a * (y * x ^ (2 - j₁))) * y * (a * (y * x ^ (2 - j₁)))⁻¹ =
            y * x ^ (2 ^ (0 + 2)) := by
        have e3 : (a * (y * x ^ (2 - j₁))) * y * (a * (y * x ^ (2 - j₁)))⁻¹ =
            a * ((y * x ^ (2 - j₁)) * y * (y * x ^ (2 - j₁))⁻¹) * a⁻¹ := by group
        rw [e3, conj_xa_y c, hconj_xa]
        obtain ⟨w₂, hw₂⟩ := aux_mul i (2 * (2 - j₁)) 3 h3
        rcases Int.even_or_odd j₁ with ⟨k, hk⟩ | ⟨k, hk⟩
        · right
          have h4 : x ^ (2 * j₁ + i * (2 * (2 - j₁))) = x ^ (2 ^ (0 + 2)) := by
            rw [← zpow_natCast, zpow_eq_zpow_iff_eight c]
            push_cast
            omega
          rw [h4]
        · left
          have h4 : x ^ (2 * j₁ + i * (2 * (2 - j₁))) = 1 := by
            rw [zpow_eq_one_iff_eight c]
            omega
          rw [h4, mul_one]
      exact T7U.isFAut_of_action_pm (n' := 0) s hV2 hbV hx hy
  ·
    obtain ⟨w, hw⟩ := aux_mul i j 5 h5
    rw [hw] at hja
    have hx : a * x * a⁻¹ = x ^ ((1 : ℤ) + 2 ^ (0 + 2)) := by
      rw [hax, zpow_eq_zpow_iff_eight c]
      norm_num
      omega
    have hy : a * y * a⁻¹ = y ∨ a * y * a⁻¹ = y * x ^ (2 ^ (0 + 2)) := by
      rcases (show j % 8 = 0 ∨ j % 8 = 4 by omega) with hj0 | hj4
      · left
        have h4 : x ^ j = 1 := by
          rw [zpow_eq_one_iff_eight c]
          omega
        rw [hay, h4, mul_one]
      · right
        have h4 : x ^ j = x ^ (2 ^ (0 + 2)) := by
          rw [← zpow_natCast, zpow_eq_zpow_iff_eight c]
          push_cast
          omega
        rw [hay, h4]
    have hF : IsFAut R a := T7U.isFAut_of_action_pm (n' := 0) s hV2 haV hx hy
    exact Or.inr ⟨1, R.one_mem, by simpa using ha2, by simpa using hF⟩
  ·
    obtain ⟨w, hw⟩ := aux_mul i j 7 h7
    by_cases hjev : Even j
    · have hcong : x ^ i = x ∨ x ^ i = x⁻¹ := by
        right
        rw [← zpow_neg_one, zpow_eq_zpow_iff_eight c]
        omega
      exact Or.inl (exists_inner_of_mem_sup (T7F2.Out.mem_sup_of_cong s haV hi hjev hax hay hcong))
    · exfalso
      have hjodd : Odd j := Int.not_even_iff_odd.mp hjev
      obtain ⟨jk, hjk⟩ := hjodd
      have hle : R ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.zpowers z := by
        rintro r ⟨hrR, hrC⟩
        have hrc : a * r * a⁻¹ = r := by
          have h := Subgroup.mem_centralizer_singleton_iff.mp hrC
          calc a * r * a⁻¹ = (r * a) * a⁻¹ := by rw [h]
            _ = r := by group
        rcases c.cover r hrR with ⟨e, rfl⟩ | ⟨e, rfl⟩
        · rw [hxi, zpow_eq_zpow_iff_eight c] at hrc
          obtain ⟨w', hw'⟩ := aux_mul i e 7 h7
          obtain ⟨u, hu⟩ : (4 : ℤ) ∣ e := by omega
          rw [hzx, hu, zpow_mul]
          exact Subgroup.zpow_mem_zpowers _ _
        · rw [hconj_xa] at hrc
          have h2 : x ^ (j + i * e) = x ^ e := mul_left_cancel hrc
          rw [zpow_eq_zpow_iff_eight c] at h2
          obtain ⟨w', hw'⟩ := aux_mul i e 7 h7
          omega
      have hcard : Nat.card ↥(R ⊓ Subgroup.centralizer ({a} : Set G)) ≤ 2 := by
        have h1 := Subgroup.card_le_of_le hle
        rw [Nat.card_zpowers] at h1
        have h2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz.sq)
        exact h1.trans (Nat.le_of_dvd (by norm_num) h2)
      omega

end Classify

end CFSG.ClassicalInvolution.Hat2A7S
