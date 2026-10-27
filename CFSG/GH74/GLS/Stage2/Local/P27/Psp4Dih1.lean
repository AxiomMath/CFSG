module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Grp

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4

open Subgroup

variable {G : Type} [Group G]

theorem mem_zpowers_of_sq {y : G} (hy : y * y = 1) {g : G} : g ∈ zpowers y ↔ g = 1 ∨ g = y := by
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
    rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · left
      rw [hm, ← two_mul, zpow_mul, zpow_two]
      simp [hy]
    · right
      rw [hm, zpow_add, zpow_mul, zpow_one, zpow_two]
      simp [hy]
  · rintro (h | h)
    · rw [h]; exact one_mem _
    · rw [h]; exact mem_zpowers _

theorem mem_sup_of_sq_comm {y₁ y₂ : G} (h1 : y₁ * y₁ = 1) (h2 : y₂ * y₂ = 1)
    (hc : y₁ * y₂ = y₂ * y₁) {g : G} :
    g ∈ zpowers y₁ ⊔ zpowers y₂ ↔ g = 1 ∨ g = y₁ ∨ g = y₂ ∨ g = y₁ * y₂ := by
  have hcomm : ∀ g ∈ zpowers y₁, ∀ g' ∈ zpowers y₂, g * g' = g' * g := by
    intro g hg g' hg'
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hg
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hg'
    exact ((show Commute y₁ y₂ from hc).zpow_zpow i j).eq
  rw [mem_sup_iff_of_commute hcomm]
  constructor
  · rintro ⟨p, hp, q, hq, rfl⟩
    rcases (mem_zpowers_of_sq h1).1 hp with h | h <;> rcases (mem_zpowers_of_sq h2).1 hq with h' | h' <;>
      rw [h, h']
    · left; exact mul_one 1
    · right; right; left; exact one_mul _
    · right; left; exact mul_one _
    · right; right; right; rfl
  · rintro (h | h | h | h)
    · exact ⟨1, one_mem _, 1, one_mem _, by rw [h, mul_one]⟩
    · exact ⟨y₁, mem_zpowers _, 1, one_mem _, by rw [h, mul_one]⟩
    · exact ⟨1, one_mem _, y₂, mem_zpowers _, by rw [h, one_mul]⟩
    · exact ⟨y₁, mem_zpowers _, y₂, mem_zpowers _, h⟩

theorem zpowers_inf_zpowers_of_sq {x w : G} (hx : x * x = 1) (hw : w * w = 1) (hne : x ≠ w) :
    zpowers x ⊓ zpowers w = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hg1, hg2⟩
  rw [mem_bot]
  rcases (mem_zpowers_of_sq hx).1 hg1 with e | e
  · exact e
  · rcases (mem_zpowers_of_sq hw).1 hg2 with e' | e'
    · exact e'
    · exact absurd (e.symm.trans e') hne

theorem card_zpowers_of_sq {y : G} (hy : y * y = 1) (hne : y ≠ 1) : Nat.card ↥(zpowers y) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact hy) hne

structure DihPair (r s : G) (M : ℕ) : Prop where
  one_le : 1 ≤ M
  ord : orderOf r = 2 * M
  s_sq : s * s = 1
  s_conj : s * r * s⁻¹ = r⁻¹

namespace DihPair

variable {r s : G} {M : ℕ}

theorem r_pow (h : DihPair r s M) : r ^ (2 * M) = 1 := h.ord ▸ pow_orderOf_eq_one r

theorem s_inv (h : DihPair r s M) : s⁻¹ = s := inv_eq_of_mul_eq_one_right h.s_sq

theorem r_ne_one (h : DihPair r s M) : r ≠ 1 := by
  intro e
  have := h.ord
  rw [e, orderOf_one] at this
  have := h.one_le
  omega

theorem zpow_eq_one_iff (h : DihPair r s M) {k : ℤ} : r ^ k = 1 ↔ ((2 * M : ℕ) : ℤ) ∣ k := by
  rw [← orderOf_dvd_iff_zpow_eq_one, h.ord]

theorem s_zpow (h : DihPair r s M) (k : ℤ) : s * r ^ k = r ^ (-k) * s :=
  mul_zpow_of_conj_inv h.s_conj k

theorem rM_sq (h : DihPair r s M) : r ^ M * r ^ M = 1 := by
  rw [← pow_add, ← two_mul]; exact h.r_pow

theorem zpow_M_neg (h : DihPair r s M) : r ^ (-(M : ℤ)) = r ^ M := by
  rw [zpow_neg, ← zpow_natCast]
  exact inv_eq_of_mul_eq_one_right (by rw [zpow_natCast]; exact h.rM_sq)

theorem zpow_half (h : DihPair r s M) {k : ℤ} (e : r ^ k * r ^ k = 1) : r ^ k = 1 ∨ r ^ k = r ^ M := by
  have h1 : r ^ (k + k) = 1 := by rw [zpow_add]; exact e
  have h2 : ((2 * M : ℕ) : ℤ) ∣ k + k := h.zpow_eq_one_iff.1 h1
  have h3 : (M : ℤ) ∣ k := by
    have : (2 : ℤ) * (M : ℤ) ∣ 2 * k := by
      have e2 : ((2 * M : ℕ) : ℤ) = 2 * (M : ℤ) := by push_cast; ring
      rw [e2] at h2
      have : k + k = 2 * k := by ring
      rwa [this] at h2
    exact Int.dvd_of_mul_dvd_mul_left (by norm_num) this
  obtain ⟨m, hm⟩ := h3
  have h4 : r ^ k ∈ zpowers (r ^ M) := by
    rw [hm, zpow_mul, zpow_natCast]
    exact zpow_mem (mem_zpowers _) m
  exact (mem_zpowers_of_sq h.rM_sq).1 h4

theorem mem_iff (h : DihPair r s M) {g : G} :
    g ∈ zpowers r ⊔ zpowers s ↔ ∃ i : ℤ, g = r ^ i ∨ g = r ^ i * s := by
  have : NeZero (2 * M) := ⟨by have := h.one_le; omega⟩
  constructor
  · intro hg
    obtain ⟨i, hi | hi⟩ := (mem_dihedral_iff (2 * M) h.r_pow h.s_sq h.s_conj).1 hg
    · exact ⟨i, Or.inl (by rw [hi, zpow_natCast])⟩
    · refine ⟨-(i : ℤ), Or.inr ?_⟩
      rw [hi, ← h.s_zpow, zpow_natCast]
  · rintro ⟨i, hi | hi⟩
    · rw [hi]
      exact mem_sup_left (zpow_mem (mem_zpowers r) i)
    · rw [hi]
      exact mul_mem (mem_sup_left (zpow_mem (mem_zpowers r) i)) (mem_sup_right (mem_zpowers s))

theorem zpow_mem_D (_h : DihPair r s M) (i : ℤ) : r ^ i ∈ zpowers r ⊔ zpowers s :=
  mem_sup_left (zpow_mem (mem_zpowers r) i)

theorem refl_mem_D (h : DihPair r s M) (i : ℤ) : r ^ i * s ∈ zpowers r ⊔ zpowers s :=
  mul_mem (h.zpow_mem_D i) (mem_sup_right (mem_zpowers s))

theorem refl_sq (h : DihPair r s M) (k : ℤ) : (r ^ k * s) * (r ^ k * s) = 1 := by
  calc (r ^ k * s) * (r ^ k * s) = r ^ k * (s * r ^ k) * s := by simp only [mul_assoc]
    _ = r ^ k * (r ^ (-k) * s) * s := by rw [h.s_zpow]
    _ = r ^ k * r ^ (-k) * (s * s) := by simp only [mul_assoc]
    _ = 1 := by rw [h.s_sq, mul_one, ← zpow_add, add_neg_cancel, zpow_zero]

theorem refl_ne_rot (_h : DihPair r s M) (hns : s ∉ zpowers r) (k j : ℤ) : r ^ k * s ≠ r ^ j := by
  intro e
  apply hns
  have e1 : s = r ^ (j - k) := by
    calc s = r ^ (-k) * (r ^ k * s) := by
          rw [← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
      _ = r ^ (-k) * r ^ j := by rw [e]
      _ = r ^ (j - k) := by rw [← zpow_add]; congr 1; ring
  have hmem := zpow_mem (mem_zpowers r) (j - k)
  rw [← e1] at hmem
  exact hmem

theorem refl_mul_refl (h : DihPair r s M) (i j : ℤ) : (r ^ i * s) * (r ^ j * s) = r ^ (i - j) := by
  calc (r ^ i * s) * (r ^ j * s) = r ^ i * (s * r ^ j) * s := by simp only [mul_assoc]
    _ = r ^ i * (r ^ (-j) * s) * s := by rw [h.s_zpow]
    _ = r ^ i * r ^ (-j) * (s * s) := by simp only [mul_assoc]
    _ = r ^ (i - j) := by rw [h.s_sq, mul_one, ← zpow_add, sub_eq_add_neg]

theorem rot_mul_refl (_h : DihPair r s M) (i j : ℤ) : r ^ i * (r ^ j * s) = r ^ (i + j) * s := by
  rw [← mul_assoc, ← zpow_add]

theorem refl_mul_rot (h : DihPair r s M) (i j : ℤ) : (r ^ i * s) * r ^ j = r ^ (i - j) * s := by
  rw [mul_assoc, h.s_zpow, ← mul_assoc, ← zpow_add, sub_eq_add_neg]

theorem conj_refl (h : DihPair r s M) {g : G} (hg : g ∈ zpowers r ⊔ zpowers s) (j : ℤ) :
    ∃ m : ℤ, g * (r ^ j * s) * g⁻¹ = r ^ (j + 2 * m) * s := by
  obtain ⟨i, hi | hi⟩ := h.mem_iff.1 hg
  · refine ⟨i, ?_⟩
    rw [hi, ← zpow_neg, h.rot_mul_refl, mul_assoc, h.s_zpow, neg_neg, ← mul_assoc, ← zpow_add]
    congr 2
    ring
  · refine ⟨i - j, ?_⟩
    have hinv : (r ^ i * s)⁻¹ = s * r ^ (-i) := by
      rw [mul_inv_rev, h.s_inv, zpow_neg]
    rw [hi, hinv, h.refl_mul_refl, h.s_zpow, neg_neg, ← mul_assoc, ← zpow_add]
    congr 2
    ring

theorem rM_comm_refl (h : DihPair r s M) (k : ℤ) :
    r ^ M * (r ^ k * s) = (r ^ k * s) * r ^ M := by
  have e : r ^ ((M : ℤ) + k) = r ^ (k - (M : ℤ)) := by
    calc r ^ ((M : ℤ) + k) = r ^ (M : ℤ) * r ^ k := zpow_add _ _ _
      _ = r ^ (-(M : ℤ)) * r ^ k := by rw [h.zpow_M_neg, zpow_natCast]
      _ = r ^ (k - (M : ℤ)) := by rw [← zpow_add, add_comm, sub_eq_add_neg]
  rw [← zpow_natCast r M, h.rot_mul_refl, h.refl_mul_rot, e]

theorem centralizer_refl (h : DihPair r s M) (k : ℤ) {g : G} (hg : g ∈ zpowers r ⊔ zpowers s) :
    g * (r ^ k * s) = (r ^ k * s) * g ↔
      g = 1 ∨ g = r ^ M ∨ g = r ^ k * s ∨ g = r ^ M * (r ^ k * s) := by
  constructor
  · intro hc
    obtain ⟨i, hi | hi⟩ := h.mem_iff.1 hg
    · rw [hi, h.rot_mul_refl, h.refl_mul_rot] at hc
      have e : r ^ (i + k) = r ^ (k - i) := mul_right_cancel hc
      have e2 : r ^ i * r ^ i = 1 := by
        calc r ^ i * r ^ i = r ^ (i + i) := (zpow_add _ _ _).symm
          _ = r ^ ((i + k) + (i - k)) := by congr 1; ring
          _ = r ^ (i + k) * r ^ (i - k) := zpow_add _ _ _
          _ = r ^ (k - i) * r ^ (i - k) := by rw [e]
          _ = r ^ ((k - i) + (i - k)) := (zpow_add _ _ _).symm
          _ = 1 := by rw [show (k - i) + (i - k) = 0 by ring, zpow_zero]
      rcases h.zpow_half e2 with h1 | h1
      · left; rw [hi, h1]
      · right; left; rw [hi, h1]
    · rw [hi, h.refl_mul_refl, h.refl_mul_refl] at hc
      have e2 : r ^ (i - k) * r ^ (i - k) = 1 := by
        calc r ^ (i - k) * r ^ (i - k) = r ^ (i - k) * r ^ (k - i) := by rw [← hc]
          _ = r ^ ((i - k) + (k - i)) := (zpow_add _ _ _).symm
          _ = 1 := by rw [show (i - k) + (k - i) = 0 by ring, zpow_zero]
      have hg' : r ^ i * s = r ^ (i - k) * (r ^ k * s) := by
        rw [h.rot_mul_refl]; congr 2; ring
      rcases h.zpow_half e2 with h1 | h1
      · right; right; left; rw [hi, hg', h1, one_mul]
      · right; right; right; rw [hi, hg', h1]
  · rintro (h1 | h1 | h1 | h1)
    · rw [h1, one_mul, mul_one]
    · rw [h1]; exact h.rM_comm_refl k
    · rw [h1]
    · rw [h1]
      calc r ^ M * (r ^ k * s) * (r ^ k * s) = (r ^ k * s) * r ^ M * (r ^ k * s) := by
            rw [h.rM_comm_refl k]
        _ = (r ^ k * s) * (r ^ M * (r ^ k * s)) := by simp only [mul_assoc]

theorem not_conj_rot_refl (h : DihPair r s M) {g : G} (hg : g ∈ zpowers r ⊔ zpowers s) (k : ℤ) :
    g * (r ^ (k + 1) * s) * g⁻¹ ≠ r ^ k * s := by
  intro e
  obtain ⟨m, hm⟩ := h.conj_refl hg (k + 1)
  rw [hm] at e
  have e1 : r ^ (k + 1 + 2 * m) = r ^ k := mul_right_cancel e
  have e2 : r ^ (1 + 2 * m) = 1 := by
    have : r ^ (k + 1 + 2 * m) = r ^ k * r ^ (1 + 2 * m) := by
      rw [← zpow_add]; congr 1; ring
    rw [this] at e1
    exact mul_left_cancel (e1.trans (mul_one _).symm)
  have e3 := h.zpow_eq_one_iff.1 e2
  have e4 : (2 : ℤ) ∣ 1 + 2 * m := dvd_trans ⟨M, by push_cast; ring⟩ e3
  omega

theorem refl_not_comm_r (h : DihPair r s M) (hM : 2 ≤ M) (j : ℤ) :
    r * (r ^ j * s) ≠ (r ^ j * s) * r := by
  intro e
  have e1 : r * (r ^ j * s) = r ^ (1 + j) * s := by
    have := h.rot_mul_refl 1 j
    rwa [zpow_one] at this
  have e2 : (r ^ j * s) * r = r ^ (j - 1) * s := by
    have := h.refl_mul_rot j 1
    rwa [zpow_one] at this
  rw [e1, e2] at e
  have e3 : r ^ (1 + j) = r ^ (j - 1) := mul_right_cancel e
  have e4 : r ^ (2 : ℤ) = 1 := by
    have : r ^ (1 + j) = r ^ (j - 1) * r ^ (2 : ℤ) := by
      rw [← zpow_add]; congr 1; ring
    rw [this] at e3
    exact mul_left_cancel (e3.trans (mul_one _).symm)
  have e5 := h.zpow_eq_one_iff.1 e4
  have e6 := Int.le_of_dvd (by norm_num) e5
  push_cast at e6
  omega

theorem central_iff (h : DihPair r s M) (hM : 2 ≤ M) {g : G} (hg : g ∈ zpowers r ⊔ zpowers s) :
    (∀ d ∈ zpowers r ⊔ zpowers s, d * g = g * d) ↔ g = 1 ∨ g = r ^ M := by
  constructor
  · intro hc
    have h0 := hc s (mem_sup_right (mem_zpowers s))
    have h0' : g * (r ^ (0 : ℤ) * s) = (r ^ (0 : ℤ) * s) * g := by
      rw [zpow_zero, one_mul]; exact h0.symm
    have hr := hc r (mem_sup_left (mem_zpowers r))
    rcases (h.centralizer_refl 0 hg).1 h0' with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso
      apply h.refl_not_comm_r hM 0
      rw [← h1]; exact hr
    · exfalso
      have e : g = r ^ ((M : ℤ) + 0) * s := by
        rw [h1, ← zpow_natCast r M, h.rot_mul_refl]
      apply h.refl_not_comm_r hM ((M : ℤ) + 0)
      rw [← e]; exact hr
  · intro hg1 d hd
    have hrM : r ^ M * r = r * r ^ M := by
      rw [← pow_succ, ← pow_succ']
    have hsM : r ^ M * s = s * r ^ M := by
      rw [← zpow_natCast r M, h.s_zpow, h.zpow_M_neg, zpow_natCast]
    have hle : zpowers r ⊔ zpowers s ≤ centralizer ({r ^ M} : Set G) := by
      refine sup_le ?_ ?_ <;> rw [zpowers_le, mem_centralizer_singleton_iff]
      · exact hrM.symm
      · exact hsM.symm
    have hd' := mem_centralizer_singleton_iff.1 (hle hd)
    rcases hg1 with e | e
    · rw [e, mul_one, one_mul]
    · rw [e]; exact hd'

end DihPair

theorem center_map_eq_of_forall {K Z : Subgroup G} (hZ : Z ≤ K)
    (h : ∀ g ∈ K, (∀ d ∈ K, d * g = g * d) → g ∈ Z) (h' : ∀ g ∈ Z, ∀ d ∈ K, d * g = g * d) :
    (center ↥K).map K.subtype = Z := by
  ext g
  constructor
  · rintro ⟨g', hg', rfl⟩
    refine h g' g'.2 (fun d hd => ?_)
    have := Subgroup.mem_center_iff.1 hg' ⟨d, hd⟩
    exact congrArg Subtype.val this
  · intro hg
    refine ⟨⟨g, hZ hg⟩, Subgroup.mem_center_iff.2 (fun d => ?_), rfl⟩
    exact Subtype.ext (h' g hg d d.2)

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4
