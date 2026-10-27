module

public import CFSG.ClassicalInvolution.Asc77.AscT7F2OutH
public import CFSG.ClassicalInvolution.Asc77.WP2Thm7c

public section

namespace CFSG.ClassicalInvolution.Asc77.T7F2

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

namespace Out

variable {G : Type} [Group G] {R N : Subgroup G} {a b : G} {n : ℕ}

variable (s : Setting R N a b n)

include s

omit s in
theorem nt_lemma (n : ℕ) (hn : 2 ≤ n) (i : ℤ) (hodd : Odd i)
    (h1 : (2 : ℤ) ^ (n + 1) ∣ i ^ 2 - 1)
    (hne1 : ¬ (2 : ℤ) ^ (n + 1) ∣ i - 1) (hne2 : ¬ (2 : ℤ) ^ (n + 1) ∣ i + 1) :
    (2 : ℤ) ^ (n + 1) ∣ i - (1 + 2 ^ n) ∨ (2 : ℤ) ^ (n + 1) ∣ i + (1 + 2 ^ n) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  obtain ⟨u, rfl⟩ := hodd
  have h2 : (2 : ℤ) ^ (n' + 1) ∣ u * (u + 1) := by
    have e : (2 * u + 1) ^ 2 - 1 = 4 * (u * (u + 1)) := by ring
    rw [e] at h1
    have e2 : (2 : ℤ) ^ (n' + 2 + 1) = 4 * 2 ^ (n' + 1) := by ring
    rw [e2] at h1
    exact (mul_dvd_mul_iff_left (by norm_num)).mp h1
  rcases Int.even_or_odd u with hu | hu
  ·
    have hcop : IsCoprime ((2 : ℤ) ^ (n' + 1)) (u + 1) := by
      apply IsCoprime.pow_left
      rw [Int.isCoprime_two_left]
      exact hu.add_one
    have hdiv : (2 : ℤ) ^ (n' + 1) ∣ u := hcop.dvd_of_dvd_mul_right h2
    obtain ⟨w, hw⟩ := hdiv
    left
    have hw_odd : Odd w := by
      by_contra hev
      rw [Int.not_odd_iff_even] at hev
      obtain ⟨t, ht⟩ := hev
      apply hne1
      refine ⟨t, ?_⟩
      have : 2 * u + 1 - 1 = 2 ^ (n' + 2) * w := by rw [hw]; ring
      rw [this, ht]; ring
    obtain ⟨t, ht⟩ := hw_odd
    refine ⟨t, ?_⟩
    rw [hw, ht]; ring
  ·
    have hcop : IsCoprime ((2 : ℤ) ^ (n' + 1)) u := by
      apply IsCoprime.pow_left
      rw [Int.isCoprime_two_left]
      exact hu
    have hdiv : (2 : ℤ) ^ (n' + 1) ∣ u + 1 := hcop.dvd_of_dvd_mul_left h2
    obtain ⟨w, hw⟩ := hdiv
    right
    have hw_odd : Odd w := by
      by_contra hev
      rw [Int.not_odd_iff_even] at hev
      obtain ⟨t, ht⟩ := hev
      apply hne2
      refine ⟨t, ?_⟩
      have : 2 * u + 1 + 1 = 2 ^ (n' + 2) * w := by
        have : u = 2 ^ (n' + 1) * w - 1 := by linarith
        rw [this]; ring
      rw [this, ht]; ring
    obtain ⟨t, ht⟩ := hw_odd
    refine ⟨t + 1, ?_⟩
    have : u = 2 ^ (n' + 1) * w - 1 := by linarith
    rw [this, ht]; ring


omit s in
theorem conj_zpow_a {m : G} {E : ℤ} (ha : m * a * m⁻¹ = a ^ E) (i : ℤ) :
    m * a ^ i * m⁻¹ = a ^ (E * i) := by
  rw [← conj_zpow, ha, ← zpow_mul]

omit s in
theorem isFAut_of_action {n' : ℕ} (s : Setting R N a b (n' + 2)) (hN2 : IsPGroup 2 N) {m : G}
    (hm : m ∈ N) (ha : m * a * m⁻¹ = a ^ ((1 : ℤ) + 2 ^ (n' + 2))) (hb : m * b * m⁻¹ = b) :
    IsFAut R m := by
  have c := s.coord
  set E : ℤ := (1 : ℤ) + 2 ^ (n' + 2) with hE
  have hEi : ∀ i : ℤ, a ^ (E * i) = a ^ i ↔ Even i := by
    intro i
    rw [c.zpow_eq_iff]
    have : E * i - i = 2 ^ (n' + 2) * i := by rw [hE]; ring
    rw [this]
    constructor
    · intro h
      have h2 : (2 : ℤ) ^ (n' + 2) * 2 ∣ 2 ^ (n' + 2) * i := by
        have : (2 : ℤ) ^ (n' + 2 + 1) = 2 ^ (n' + 2) * 2 := by ring
        rw [← this]; exact h
      exact even_iff_two_dvd.mpr ((mul_dvd_mul_iff_left (by positivity)).mp h2)
    · rintro ⟨t, rfl⟩
      exact ⟨t, by ring⟩
  have hnorm : m ∈ Subgroup.normalizer (R : Set G) := mem_normalizer_iff_conjSub_eq.mpr (s.hNR m hm)
  have hsq : ∀ k ∈ R, m * m * k = k * (m * m) := by
    have hmma : (m * m) * a * (m * m)⁻¹ = a := by
      rw [coord_mul_a ha ha]
      have : a ^ (E * E) = a ^ (1 : ℤ) := by
        rw [c.zpow_eq_iff]
        refine ⟨1 + 2 ^ (n' + 1), ?_⟩
        rw [hE]; ring
      simpa using this
    have hmmb : (m * m) * b * (m * m)⁻¹ = b := by
      calc (m * m) * b * (m * m)⁻¹ = m * (m * b * m⁻¹) * m⁻¹ := by group
        _ = b := by rw [hb, hb]
    intro k hk
    exact (centralizes_of_fixes c hmma hmmb k hk).symm
  set Q : Subgroup G := R ⊓ Subgroup.centralizer ({m} : Set G) with hQ
  have hmQ : ∀ x : G, x ∈ Q ↔ x ∈ R ∧ m * x * m⁻¹ = x := by
    intro x
    rw [hQ, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
    exact and_congr_right fun _ => eq_comm
  have hQ2 : IsPGroup 2 Q := hN2.to_le (inf_le_left.trans s.hRN)
  have haa : a * a ∈ Q := by
    refine (hmQ _).mpr ⟨R.mul_mem c.ha c.ha, ?_⟩
    have h1 : m * (a * a) * m⁻¹ = (m * a * m⁻¹) * (m * a * m⁻¹) := by group
    rw [h1, ha, ← zpow_add]
    have : a ^ (E + E) = a ^ ((2 : ℤ)) := by
      rw [c.zpow_eq_iff]
      refine ⟨1, ?_⟩
      rw [hE]; ring
    rw [this, zpow_two]
  have hbQ : b ∈ Q := (hmQ _).mpr ⟨c.hb, hb⟩
  have hcQ : QuatCoord Q (a * a) b (n' + 1) := by
    refine ⟨haa, hbQ, ?_, by omega, ?_, ?_, ?_⟩
    · calc b * (a * a) * b⁻¹ = (b * a * b⁻¹) * (b * a * b⁻¹) := by group
        _ = (a * a)⁻¹ := by rw [c.hbab]; group
    · have h1 : a * a = a ^ 2 := (pow_two a).symm
      rw [h1, orderOf_pow_of_dvd (by norm_num) (by rw [c.hord]; exact ⟨2 ^ (n' + 2), by ring⟩),
        c.hord]
      have : (2 : ℕ) ^ (n' + 2 + 1) = 2 ^ (n' + 1 + 1) * 2 := by ring
      rw [this, Nat.mul_div_cancel _ (by norm_num)]
    · have h1 : (a * a) ^ (2 ^ (n' + 1)) = a ^ (2 ^ (n' + 2)) := by
        rw [← pow_two, ← pow_mul]
        congr 1
        ring
      rw [h1]
      exact c.hbb
    · intro r hr
      obtain ⟨hrR, hrm⟩ := (hmQ r).mp hr
      have e2 : a * a = a ^ (2 : ℤ) := (zpow_two a).symm
      rcases c.cover r hrR with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · left
        have h1 : a ^ (E * i) = a ^ i := by rw [← conj_zpow_a ha i, hrm]
        obtain ⟨t, ht⟩ := (hEi i).mp h1
        refine ⟨t, ?_⟩
        rw [ht, e2, ← zpow_mul]
        congr 1; ring
      · right
        have h1 : b * a ^ (E * i) = b * a ^ i := by
          calc b * a ^ (E * i) = (m * b * m⁻¹) * (m * a ^ i * m⁻¹) := by
                rw [hb, conj_zpow_a ha i]
            _ = m * (b * a ^ i) * m⁻¹ := by group
            _ = b * a ^ i := hrm
        obtain ⟨t, ht⟩ := (hEi i).mp (mul_left_cancel h1)
        refine ⟨t, ?_⟩
        rw [ht, e2, ← zpow_mul]
        congr 2; ring
  have hR2 : IsPGroup 2 R := hN2.to_le s.hRN
  refine ⟨hnorm, hsq, Q, R, ⟨le_rfl, hQ2, fun V' hV'Q _ hle => le_antisymm hV'Q hle⟩,
    hcQ.isQuatSub, ⟨le_rfl, hR2, fun V' hV'R _ hle => le_antisymm hV'R hle⟩, ?_⟩
  rw [c.natCard, hcQ.natCard]
  ring


omit s in
theorem exists_mul_of_mem_sup_of_commute {A B : Subgroup G}
    (h : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) {v : G} (hv : v ∈ A ⊔ B) :
    ∃ x ∈ A, ∃ y ∈ B, v = x * y := by
  let P : Subgroup G :=
    { carrier := {v | ∃ x ∈ A, ∃ y ∈ B, v = x * y}
      mul_mem' := by
        rintro _ _ ⟨x₁, hx₁, y₁, hy₁, rfl⟩ ⟨x₂, hx₂, y₂, hy₂, rfl⟩
        refine ⟨x₁ * x₂, A.mul_mem hx₁ hx₂, y₁ * y₂, B.mul_mem hy₁ hy₂, ?_⟩
        calc x₁ * y₁ * (x₂ * y₂) = x₁ * (y₁ * x₂) * y₂ := by group
          _ = x₁ * (x₂ * y₁) * y₂ := by rw [← h x₂ hx₂ y₁ hy₁]
          _ = x₁ * x₂ * (y₁ * y₂) := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨x, hx, y, hy, rfl⟩
        refine ⟨x⁻¹, A.inv_mem hx, y⁻¹, B.inv_mem hy, ?_⟩
        have h1 := h x hx y hy
        have : x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ := by
          rw [← mul_inv_rev, ← mul_inv_rev, h1]
        rw [mul_inv_rev, this] }
  have hle : A ⊔ B ≤ P :=
    sup_le (fun x hx => ⟨x, hx, 1, B.one_mem, by simp⟩)
      (fun y hy => ⟨1, A.one_mem, y, hy, by simp⟩)
  exact hle hv

theorem mem_sup_of_sq_mem (hF : ∀ y ∈ N, ¬ IsFAut R y) (hN2 : IsPGroup 2 N) {m : G}
    (hm : m ∈ Hsub s) (hsq : m * m ∈ R ⊔ (N ⊓ Subgroup.centralizer (R : Set G))) :
    m ∈ R ⊔ (N ⊓ Subgroup.centralizer (R : Set G)) := by
  have c := s.coord
  obtain ⟨hmN, j, hj, hb⟩ := hm
  obtain ⟨i, -, hi, ha, -⟩ := s.coord_of_mem hmN
  by_cases hcong : a ^ i = a ∨ a ^ i = a⁻¹
  · exact mem_sup_of_cong s hmN hi hj ha hb hcong
  exfalso
  push Not at hcong
  obtain ⟨hne1, hne2⟩ := hcong
  have hne1' : ¬ (2 : ℤ) ^ (n + 1) ∣ i - 1 := by
    intro h
    apply hne1
    have : a ^ i = a ^ (1 : ℤ) := by rw [c.zpow_eq_iff]; simpa using h
    simpa using this
  have hne2' : ¬ (2 : ℤ) ^ (n + 1) ∣ i + 1 := by
    intro h
    apply hne2
    have : a ^ i = a ^ (-1 : ℤ) := by rw [c.zpow_eq_iff]; simpa [sub_neg_eq_add] using h
    simpa using this
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn1 : n = 1 := by have := c.hn; omega
    subst hn1
    obtain ⟨u, rfl⟩ := hi
    rcases Int.even_or_odd u with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact hne1' ⟨t, by rw [ht]; ring⟩
    · exact hne2' ⟨t + 1, by rw [ht]; ring⟩
  have hcomm : ∀ x ∈ R, ∀ y ∈ N ⊓ Subgroup.centralizer (R : Set G), x * y = y * x :=
    fun x hx y hy => Subgroup.mem_centralizer_iff.mp hy.2 x hx
  obtain ⟨r, hr, c', hc', hmm⟩ := exists_mul_of_mem_sup_of_commute hcomm hsq
  have hc'a : c' * a = a * c' := (Subgroup.mem_centralizer_iff.mp hc'.2 a c.ha).symm
  have hsqa : (m * m) * a * (m * m)⁻¹ = a ^ (i * i) := coord_mul_a ha ha
  have hra : (a ^ (i * i) = a) ∨ (a ^ (i * i) = a⁻¹) := by
    have e : (m * m) * a * (m * m)⁻¹ = r * a * r⁻¹ := by
      rw [hmm]
      calc r * c' * a * (r * c')⁻¹ = r * (c' * a * c'⁻¹) * r⁻¹ := by group
        _ = r * a * r⁻¹ := by rw [mul_inv_eq_iff_eq_mul.mpr hc'a]
    rw [← hsqa, e]
    rcases c.cover r hr with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · left
      rw [(Commute.zpow_left (Commute.refl a) k).eq]; group
    · right
      calc b * a ^ k * a * (b * a ^ k)⁻¹ = b * (a ^ k * a * (a ^ k)⁻¹) * b⁻¹ := by group
        _ = b * a * b⁻¹ := by rw [(Commute.zpow_left (Commute.refl a) k).eq]; group
        _ = a⁻¹ := c.hbab
  have hsq1 : (2 : ℤ) ^ (n + 1) ∣ i ^ 2 - 1 := by
    rcases hra with h | h
    · have : a ^ (i * i) = a ^ (1 : ℤ) := by simpa using h
      rw [c.zpow_eq_iff] at this
      simpa [sq] using this
    · exfalso
      have : a ^ (i * i) = a ^ (-1 : ℤ) := by simpa using h
      rw [c.zpow_eq_iff] at this
      have h8 : (8 : ℤ) ∣ i * i + 1 := by
        have h2 : (8 : ℤ) ∣ (2 : ℤ) ^ (n + 1) := by
          have : (2 : ℤ) ^ (n + 1) = 2 ^ 3 * 2 ^ (n - 2) := by
            rw [← pow_add]; congr 1; omega
          rw [this]; exact dvd_mul_of_dvd_left (by norm_num) _
        exact h2.trans (by simpa using this)
      obtain ⟨u, rfl⟩ := hi
      obtain ⟨w, hw⟩ := Int.even_mul_succ_self u
      have e : (2 * u + 1) * (2 * u + 1) + 1 = 8 * w + 2 := by linear_combination 4 * hw
      rw [e] at h8
      omega
  rcases nt_lemma n hn2 i hi hsq1 hne1' hne2' with h | h
  ·
    obtain ⟨k, hka, hkb⟩ := adjust c hi hj ha hb
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
    have hai : a ^ i = a ^ ((1 : ℤ) + 2 ^ (n' + 2)) := by
      rw [c.zpow_eq_iff]; simpa using h
    exact hF (m * a ^ k) (N.mul_mem hmN (s.hRN (R.zpow_mem c.ha k)))
      (isFAut_of_action s hN2 (N.mul_mem hmN (s.hRN (R.zpow_mem c.ha k)))
        (by rw [hka, hai]) hkb)
  ·
    obtain ⟨k, hka, hkb⟩ := adjust c hi hj ha hb
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
    have hai : a ^ (-i) = a ^ ((1 : ℤ) + 2 ^ (n' + 2)) := by
      rw [c.zpow_eq_iff]
      have : (2 : ℤ) ^ (n' + 2 + 1) ∣ -i - (1 + 2 ^ (n' + 2)) := by
        have := dvd_neg.mpr h
        convert this using 1; ring
      exact this
    have hm₂ : m * a ^ k * b ∈ N :=
      N.mul_mem (N.mul_mem hmN (s.hRN (R.zpow_mem c.ha k))) (s.hRN c.hb)
    refine hF _ hm₂ (isFAut_of_action s hN2 hm₂ ?_ ?_)
    · calc (m * a ^ k * b) * a * (m * a ^ k * b)⁻¹
          = (m * a ^ k) * (b * a * b⁻¹) * (m * a ^ k)⁻¹ := by group
        _ = (m * a ^ k) * a⁻¹ * (m * a ^ k)⁻¹ := by rw [c.hbab]
        _ = ((m * a ^ k) * a * (m * a ^ k)⁻¹)⁻¹ := by group
        _ = a ^ (-i) := by rw [hka, zpow_neg]
        _ = a ^ ((1 : ℤ) + 2 ^ (n' + 2)) := hai
    · calc (m * a ^ k * b) * b * (m * a ^ k * b)⁻¹ = (m * a ^ k) * b * (m * a ^ k)⁻¹ := by group
        _ = b := hkb


theorem Hsub_le_sup (hF : ∀ y ∈ N, ¬ IsFAut R y) (hN2 : IsPGroup 2 N) :
    Hsub s ≤ R ⊔ (N ⊓ Subgroup.centralizer (R : Set G)) := by
  suffices h : ∀ k : ℕ, ∀ m ∈ Hsub s, orderOf m = k →
      m ∈ R ⊔ (N ⊓ Subgroup.centralizer (R : Set G)) from fun m hm => h _ m hm rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m hm hk
    by_cases h1 : k = 1
    · subst h1
      rw [orderOf_eq_one_iff.mp hk]
      exact Subgroup.one_mem _
    have hmN : m ∈ N := hm.1
    obtain ⟨t, ht⟩ := (IsPGroup.iff_orderOf.mp hN2) ⟨m, hmN⟩
    have ht' : orderOf m = 2 ^ t := by simpa using ht
    have ht1 : t ≠ 0 := by
      rintro rfl
      exact h1 (hk.symm.trans (by simpa using ht'))
    have hdvd : 2 ∣ orderOf m := by
      rw [ht']; exact dvd_pow_self 2 ht1
    have hlt : orderOf (m * m) < k := by
      rw [← pow_two, orderOf_pow_of_dvd (by norm_num) hdvd, hk]
      have : 0 < k := by rw [← hk, ht']; positivity
      omega
    have hmm : m * m ∈ R ⊔ (N ⊓ Subgroup.centralizer (R : Set G)) :=
      ih _ hlt (m * m) ((Hsub s).mul_mem hm hm) rfl
    exact mem_sup_of_sq_mem s hF hN2 hm hmm

theorem relIndex_sup_le (hF : ∀ y ∈ N, ¬ IsFAut R y) (hN2 : IsPGroup 2 N) :
    (R ⊔ (N ⊓ Subgroup.centralizer (R : Set G))).relIndex N ≤ 2 := by
  have hle := Hsub_le_sup s hF hN2
  have heq : Hsub s = R ⊔ (N ⊓ Subgroup.centralizer (R : Set G)) :=
    le_antisymm hle (sup_le_Hsub s)
  rw [← heq]
  exact Hsub_relIndex_le s

end Out

section Main

variable {G : Type} [Group G] [Finite G] {R N : Subgroup G} {z : G}

theorem relIndex_sup_centralizer_le_two (hR : IsQuatSub R) (hz : IsUniqueInvolution R z)
    (hRN : R ≤ N) (hN2 : IsPGroup 2 N) (hNR : ∀ y ∈ N, conjSub y R = R)
    (hF : ∀ y ∈ N, ¬ IsFAut R y) :
    (R ⊔ (N ⊓ Subgroup.centralizer (R : Set G))).relIndex N ≤ 2 := by
  obtain ⟨a, b, n, c, hinv⟩ := exists_coord hR hz hN2 hNR
  exact Out.relIndex_sup_le ⟨c, hRN, hNR, hinv⟩ hF hN2

end Main

end CFSG.ClassicalInvolution.Asc77.T7F2
