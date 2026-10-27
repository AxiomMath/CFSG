module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic3

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

open Subgroup

structure S4Data {G : Type*} [Group G] (h t e e₁ e₂ : G) (m : ℕ) : Prop where
  hord : orderOf h = 3 ^ (m + 1)
  ht2 : t * t = 1
  hth : t * h * t⁻¹ = h⁻¹
  he2 : e * e = 1
  he₁2 : e₁ * e₁ = 1
  he₂2 : e₂ * e₂ = 1
  c₁ : e * e₁ = e₁ * e
  c₂ : e * e₂ = e₂ * e
  c₃ : e₁ * e₂ = e₂ * e₁
  prod : e * e₁ * e₂ = 1
  hh₀ : h⁻¹ * e * h = e₁
  hh₁ : h⁻¹ * e₁ * h = e₂
  hh₂ : h⁻¹ * e₂ * h = e
  ht₀ : t * e * t⁻¹ = e
  ht₁ : t * e₁ * t⁻¹ = e₂
  ht₂ : t * e₂ * t⁻¹ = e₁
  ne₀ : e ≠ 1
  ne₁ : e₁ ≠ 1
  ne₂ : e₂ ≠ 1
  n₀₁ : e ≠ e₁
  n₀₂ : e ≠ e₂
  n₁₂ : e₁ ≠ e₂

theorem mem_ker_coset {G : Type*} [Group G] {Sg H : Subgroup G} {g : ↥Sg} :
    g ∈ (MulAction.toPermHom ↥Sg (↥Sg ⧸ H.subgroupOf Sg)).ker ↔
      ∀ a : ↥Sg, (a : G)⁻¹ * (g : G)⁻¹ * (a : G) ∈ H := by
  rw [MonoidHom.mem_ker, Equiv.Perm.ext_iff]
  constructor
  · intro h a
    have h1 := h (QuotientGroup.mk a)
    have h2 : (QuotientGroup.mk (g * a) : ↥Sg ⧸ H.subgroupOf Sg) = QuotientGroup.mk a := h1
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h2
    simpa [mul_assoc] using h2
  · intro h x
    induction x using QuotientGroup.induction_on with
    | H a =>
      show (QuotientGroup.mk (g * a) : ↥Sg ⧸ H.subgroupOf Sg) = QuotientGroup.mk a
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa [mul_assoc] using h a

namespace S4Data

section Basic

variable {G : Type*} [Group G] {h t e e₁ e₂ : G} {m : ℕ} (hD : S4Data h t e e₁ e₂ m)

include hD

theorem e₂_eq : e₂ = e * e₁ := by
  have h1 : e₂ = (e * e₁)⁻¹ := eq_inv_of_mul_eq_one_right hD.prod
  rw [h1, mul_inv_rev, inv_eq_of_mul_eq_one_right hD.he₁2, inv_eq_of_mul_eq_one_right hD.he2, hD.c₁]

theorem mem_E₀ {x : G} : x ∈ zpowers e ⊔ zpowers e₁ ↔ x = 1 ∨ x = e ∨ x = e₁ ∨ x = e₂ := by
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute' (A := zpowers e) (B := zpowers e₁)
      (fun a ha b hb => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact (Commute.zpow_zpow (show Commute e e₁ from hD.c₁) i j).eq) hx
    rcases (mem_zpowers_of_sq' hD.he2).1 ha with h1 | h1 <;>
      rcases (mem_zpowers_of_sq' hD.he₁2).1 hb with h2 | h2
    · left; rw [h1, h2]; simp
    · right; right; left; rw [h1, h2]; simp
    · right; left; rw [h1, h2]; simp
    · right; right; right; rw [h1, h2]; exact hD.e₂_eq.symm
  · rintro (h1 | h1 | h1 | h1)
    · rw [h1]; exact one_mem _
    · rw [h1]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · rw [h1]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · rw [h1, hD.e₂_eq]
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem hconj_e : h * e * h⁻¹ = e₂ := by
  have := congrArg (fun x => h * x * h⁻¹) hD.hh₂
  simpa [mul_assoc] using this.symm

theorem hconj_e₁ : h * e₁ * h⁻¹ = e := by
  have := congrArg (fun x => h * x * h⁻¹) hD.hh₀
  simpa [mul_assoc] using this.symm

theorem hconj_e₂ : h * e₂ * h⁻¹ = e₁ := by
  have := congrArg (fun x => h * x * h⁻¹) hD.hh₁
  simpa [mul_assoc] using this.symm

theorem hinv_conj {x : G} (hx : x ∈ zpowers e ⊔ zpowers e₁) : h⁻¹ * x * h ∈ zpowers e ⊔ zpowers e₁ := by
  rcases (hD.mem_E₀).1 hx with h1 | h1 | h1 | h1 <;> rw [h1] <;> (rw [hD.mem_E₀])
  · left; group
  · right; right; left; exact hD.hh₀
  · right; right; right; exact hD.hh₁
  · right; left; exact hD.hh₂

theorem h_conj {x : G} (hx : x ∈ zpowers e ⊔ zpowers e₁) : h * x * h⁻¹ ∈ zpowers e ⊔ zpowers e₁ := by
  rcases (hD.mem_E₀).1 hx with h1 | h1 | h1 | h1 <;> rw [h1] <;> (rw [hD.mem_E₀])
  · left; group
  · right; right; right; exact hD.hconj_e
  · right; left; exact hD.hconj_e₁
  · right; right; left; exact hD.hconj_e₂

theorem t_conj {x : G} (hx : x ∈ zpowers e ⊔ zpowers e₁) : t * x * t⁻¹ ∈ zpowers e ⊔ zpowers e₁ := by
  rcases (hD.mem_E₀).1 hx with h1 | h1 | h1 | h1 <;> rw [h1] <;> (rw [hD.mem_E₀])
  · left; group
  · right; left; exact hD.ht₀
  · right; right; right; exact hD.ht₁
  · right; right; left; exact hD.ht₂

theorem h3conj {x : G} (hx : x ∈ zpowers e ⊔ zpowers e₁) :
    h⁻¹ * (h⁻¹ * (h⁻¹ * x * h) * h) * h = x := by
  rcases (hD.mem_E₀).1 hx with h1 | h1 | h1 | h1 <;> rw [h1]
  · group
  · rw [hD.hh₀, hD.hh₁, hD.hh₂]
  · rw [hD.hh₁, hD.hh₂, hD.hh₀]
  · rw [hD.hh₂, hD.hh₀, hD.hh₁]

theorem h3_cent {x : G} (hx : x ∈ zpowers e ⊔ zpowers e₁) : h ^ 3 * x = x * h ^ 3 := by
  have h4 := hD.h3conj hx
  have e3 : h ^ 3 = h * h * h := by simp only [pow_succ, pow_zero, one_mul]
  rw [e3]
  calc h * h * h * x = h * h * h * (h⁻¹ * (h⁻¹ * (h⁻¹ * x * h) * h) * h) := by rw [h4]
    _ = x * (h * h * h) := by group

theorem H_le_normalizer :
    zpowers h ⊔ zpowers t ≤ normalizer ((zpowers e ⊔ zpowers e₁ : Subgroup G) : Set G) := by
  apply sup_le
  · rw [zpowers_le, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hD.h_conj hx
    · intro hx
      have := hD.hinv_conj hx
      have e : h⁻¹ * (h * x * h⁻¹) * h = x := by group
      rwa [e] at this
  · rw [zpowers_le]
    apply mem_normalizer_of_invol hD.ht2
    intro p hp
    exact hD.t_conj hp

theorem h_sq_ne : h * h ≠ 1 := by
  intro h1
  have h2 : h ^ 2 = 1 := by rw [pow_two]; exact h1
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [hD.hord] at h3
  have h4 := Nat.le_of_dvd (by norm_num) h3
  have h5 : 3 ^ 1 ≤ 3 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem t_ne_one : t ≠ 1 := by
  intro h1
  have h2 := hD.hth
  rw [h1] at h2
  apply hD.h_sq_ne
  have : h = h⁻¹ := by simpa using h2
  exact mul_eq_one_iff_eq_inv.2 this

theorem t_normalizes_h : zpowers t ≤ normalizer ((zpowers h : Subgroup G) : Set G) := by
  rw [zpowers_le]
  apply mem_normalizer_of_invol hD.ht2
  intro p hp
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
  have h1 : t * h ^ i * t⁻¹ = (h⁻¹) ^ i := by
    have := map_zpow (MulAut.conj t) h i
    simpa [MulAut.conj_apply, hD.hth] using this
  rw [h1]
  exact Subgroup.zpow_mem _ (inv_mem (Subgroup.mem_zpowers h)) i

theorem zpowers_h_inf_t : zpowers h ⊓ zpowers t = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rcases (mem_zpowers_of_sq' hD.ht2).1 hx.2 with h1 | h1
  · rw [h1]
    exact one_mem _
  · exfalso
    have hth' : t ∈ zpowers h := h1 ▸ hx.1
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hth'
    have hcomm : h * t = t * h := by
      rw [← hi]
      exact ((Commute.refl h).zpow_right i).eq
    have e1 : t * h * t⁻¹ = h := by
      rw [← hcomm]
      group
    have h3 := hD.hth
    rw [e1] at h3
    exact hD.h_sq_ne (mul_eq_one_iff_eq_inv.2 h3)

theorem card_H : Nat.card ↥(zpowers h ⊔ zpowers t) = 2 * 3 ^ (m + 1) := by
  have h1 := card_sup_mul_card_inf' (A := zpowers h) (B := zpowers t) hD.t_normalizes_h
  rw [hD.zpowers_h_inf_t, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hD.hord,
    orderOf_eq_prime (by rw [pow_two]; exact hD.ht2) hD.t_ne_one] at h1
  omega

theorem card_E₀ : Nat.card ↥(zpowers e ⊔ zpowers e₁) = 4 := by
  have hc : ∀ a ∈ zpowers e, ∀ b ∈ zpowers e₁, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow (show Commute e e₁ from hD.c₁) i j).eq
  have h1 := card_sup_mul_card_inf' (A := zpowers e) (B := zpowers e₁) (le_normalizer_of_commute' hc)
  have hbot : zpowers e ⊓ zpowers e₁ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases (mem_zpowers_of_sq' hD.he2).1 hx.1 with h2 | h2
    · rw [h2]
      exact one_mem _
    · exfalso
      rcases (mem_zpowers_of_sq' hD.he₁2).1 hx.2 with h3 | h3
      · exact hD.ne₀ (h2.symm.trans h3)
      · exact hD.n₀₁ (h2.symm.trans h3)
  rw [hbot, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers,
    orderOf_eq_prime (by rw [pow_two]; exact hD.he2) hD.ne₀,
    orderOf_eq_prime (by rw [pow_two]; exact hD.he₁2) hD.ne₁] at h1
  omega

theorem card_Sg (hEH : (zpowers e ⊔ zpowers e₁) ⊓ (zpowers h ⊔ zpowers t) = ⊥) :
    Nat.card ↥((zpowers e ⊔ zpowers e₁) ⊔ (zpowers h ⊔ zpowers t)) = 8 * 3 ^ (m + 1) := by
  have h1 := card_sup_mul_card_inf' (A := zpowers e ⊔ zpowers e₁) (B := zpowers h ⊔ zpowers t)
    hD.H_le_normalizer
  rw [hEH, Subgroup.card_bot, mul_one, hD.card_E₀, hD.card_H] at h1
  omega

theorem hzpow_conj {x : G} (hx : x ∈ zpowers e ⊔ zpowers e₁) (q r : ℤ) :
    h ^ (3 * q + r) * x * (h ^ (3 * q + r))⁻¹ = h ^ r * x * (h ^ r)⁻¹ := by
  have hc : ((h ^ 3) ^ q : G) * x * ((h ^ 3) ^ q)⁻¹ = x := by
    have h1 : Commute (h ^ 3) x := hD.h3_cent hx
    have h2 : Commute ((h ^ 3) ^ q) x := h1.zpow_left q
    rw [h2.eq]
    group
  have e1 : h ^ (3 * q + r) = h ^ r * (h ^ 3) ^ q := by
    rw [add_comm, zpow_add, zpow_mul]
    simp
  rw [e1]
  calc h ^ r * (h ^ 3) ^ q * x * (h ^ r * (h ^ 3) ^ q)⁻¹
      = h ^ r * (((h ^ 3) ^ q) * x * ((h ^ 3) ^ q)⁻¹) * (h ^ r)⁻¹ := by group
    _ = h ^ r * x * (h ^ r)⁻¹ := by rw [hc]

theorem cent_H {g : G} (hg : g ∈ zpowers h ⊔ zpowers t) (hge : g * e = e * g)
    (hge₁ : g * e₁ = e₁ * g) : g ∈ zpowers (h ^ 3) := by
  have hgx : ∀ x : G, g * x = x * g → g * x * g⁻¹ = x := fun x hx => by
    calc g * x * g⁻¹ = (x * g) * g⁻¹ := by rw [hx]
      _ = x := by group
  have hE : e ∈ zpowers e ⊔ zpowers e := by exact Subgroup.mem_sup_left (Subgroup.mem_zpowers e)
  have hEe : e ∈ zpowers e ⊔ zpowers e₁ := Subgroup.mem_sup_left (Subgroup.mem_zpowers e)
  have hEe₁ : e₁ ∈ zpowers e ⊔ zpowers e₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers e₁)
  obtain ⟨b, hb, a, ha, rfl⟩ := mem_sup_of_le_normalizer' (A := zpowers t) (B := zpowers h)
    hD.t_normalizes_h (sup_comm (zpowers h) (zpowers t) ▸ hg)
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  obtain ⟨q, r, hr0, hr3, hi⟩ : ∃ q r : ℤ, 0 ≤ r ∧ r < 3 ∧ i = 3 * q + r :=
    ⟨i / 3, i % 3, by omega, by omega, by omega⟩
  have hge' := hgx e hge
  have hge₁' := hgx e₁ hge₁
  have c0 := hD.hzpow_conj hEe q r
  have c1 := hD.hzpow_conj hEe₁ q r
  subst hi
  rcases (mem_zpowers_of_sq' hD.ht2).1 hb with hb1 | hb1
  ·
    subst hb1
    have hconj : h ^ (3 * q + r) * e * (h ^ (3 * q + r))⁻¹ = e := by simpa using hge'
    rw [c0] at hconj
    interval_cases r
    ·
      have : h ^ (3 * q + 0) = (h ^ 3) ^ q := by
        rw [add_zero, zpow_mul]
        simp
      simp only [one_mul] at *
      rw [this]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) q
    · exfalso
      simp only [zpow_one] at hconj
      exact hD.n₀₂ (hconj.symm.trans hD.hconj_e)
    · exfalso
      have h2 : h ^ (2 : ℤ) * e * (h ^ (2 : ℤ))⁻¹ = e₁ := by
        rw [zpow_two]
        calc h * h * e * (h * h)⁻¹ = h * (h * e * h⁻¹) * h⁻¹ := by group
          _ = e₁ := by rw [hD.hconj_e, hD.hconj_e₂]
      exact hD.n₀₁ (hconj.symm.trans h2)
  ·
    rw [hb1] at hge' hge₁'
    have hA : t * (h ^ (3 * q + r) * e * (h ^ (3 * q + r))⁻¹) * t⁻¹ = e := by
      calc t * (h ^ (3 * q + r) * e * (h ^ (3 * q + r))⁻¹) * t⁻¹
          = (t * h ^ (3 * q + r)) * e * (t * h ^ (3 * q + r))⁻¹ := by group
        _ = e := hge'
    have hB : t * (h ^ (3 * q + r) * e₁ * (h ^ (3 * q + r))⁻¹) * t⁻¹ = e₁ := by
      calc t * (h ^ (3 * q + r) * e₁ * (h ^ (3 * q + r))⁻¹) * t⁻¹
          = (t * h ^ (3 * q + r)) * e₁ * (t * h ^ (3 * q + r))⁻¹ := by group
        _ = e₁ := hge₁'
    rw [c0] at hA
    rw [c1] at hB
    exfalso
    interval_cases r
    · simp only [zpow_zero, one_mul, inv_one, mul_one] at hB
      exact hD.n₁₂ (hD.ht₁.symm.trans hB).symm
    · simp only [zpow_one] at hA
      rw [hD.hconj_e, hD.ht₂] at hA
      exact hD.n₀₁ hA.symm
    · have h2 : h ^ (2 : ℤ) * e * (h ^ (2 : ℤ))⁻¹ = e₁ := by
        rw [zpow_two]
        calc h * h * e * (h * h)⁻¹ = h * (h * e * h⁻¹) * h⁻¹ := by group
          _ = e₁ := by rw [hD.hconj_e, hD.hconj_e₂]
      rw [h2, hD.ht₁] at hA
      exact hD.n₀₂ hA.symm

theorem H_normalizes_h3 :
    zpowers h ⊔ zpowers t ≤ normalizer ((zpowers (h ^ 3) : Subgroup G) : Set G) := by
  apply sup_le
  · apply le_normalizer_of_commute'
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow (show Commute (h ^ 3) h from (Commute.refl h).pow_left 3) i j).eq
  · rw [zpowers_le]
    apply mem_normalizer_of_invol hD.ht2
    intro p hp
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
    have h1 : t * (h ^ 3) ^ i * t⁻¹ = ((h ^ 3)⁻¹) ^ i := by
      have := map_zpow (MulAut.conj t) (h ^ 3) i
      rw [map_pow] at this
      simpa [MulAut.conj_apply, hD.hth, inv_pow] using this
    rw [h1]
    exact Subgroup.zpow_mem _ (inv_mem (Subgroup.mem_zpowers _)) i

omit hD in
theorem h3_le_H : zpowers (h ^ 3) ≤ zpowers h ⊔ zpowers t := by
  rw [zpowers_le]
  exact Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers h) 3)

theorem card_zpowers_h3 : Nat.card ↥(zpowers (h ^ 3)) = 3 ^ m := by
  rw [Nat.card_zpowers, orderOf_pow_of_dvd (by norm_num) (by rw [hD.hord]; exact dvd_pow_self 3 (by omega)),
    hD.hord, pow_succ, Nat.mul_div_cancel _ (by norm_num)]

theorem iso [Finite G] (hEH : (zpowers e ⊔ zpowers e₁) ⊓ (zpowers h ⊔ zpowers t) = ⊥) :
    ∃ _ : ((zpowers (h ^ 3)).subgroupOf ((zpowers e ⊔ zpowers e₁) ⊔ (zpowers h ⊔ zpowers t))).Normal,
      Nonempty (↥((zpowers e ⊔ zpowers e₁) ⊔ (zpowers h ⊔ zpowers t)) ⧸
        (zpowers (h ^ 3)).subgroupOf ((zpowers e ⊔ zpowers e₁) ⊔ (zpowers h ⊔ zpowers t)) ≃*
          Equiv.Perm (Fin 4)) := by
  set E : Subgroup G := zpowers e ⊔ zpowers e₁ with hE
  set H : Subgroup G := zpowers h ⊔ zpowers t with hH
  set Sg : Subgroup G := E ⊔ H with hSg
  have hESg : E ≤ Sg := le_sup_left
  have hHSg : H ≤ Sg := le_sup_right
  have hHN : H ≤ normalizer (E : Set G) := hD.H_le_normalizer
  have hdec : ∀ a ∈ Sg, ∃ n ∈ H, ∃ e₀ ∈ E, a = n * e₀ := fun a ha =>
    mem_sup_of_le_normalizer' hHN (sup_comm E H ▸ ha)
  have hEe : e ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers e)
  have hEe₁ : e₁ ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers e₁)
  have hHnorm : ∀ n ∈ H, ∀ x ∈ E, n * x * n⁻¹ ∈ E := fun n hn x hx =>
    (Subgroup.mem_normalizer_iff.1 (hHN hn) x).1 hx
  have hker : ∀ g : ↥Sg, g ∈ (MulAction.toPermHom ↥Sg (↥Sg ⧸ H.subgroupOf Sg)).ker ↔
      (g : G) ∈ zpowers (h ^ 3) := by
    intro g
    rw [mem_ker_coset]
    constructor
    · intro hg
      have hgH : (g : G) ∈ H := by
        have := hg 1
        simpa using this
      have hcomm : ∀ x ∈ E, (g : G) * x = x * (g : G) := by
        intro x hx
        have h1 := hg ⟨x, hESg hx⟩
        have h2 : x⁻¹ * (g : G)⁻¹ * x * (g : G) ∈ H := mul_mem h1 hgH
        have h3 : x⁻¹ * (g : G)⁻¹ * x * (g : G) ∈ E := by
          have := mul_mem (inv_mem hx) (hHnorm _ (inv_mem hgH) x hx)
          have e1 : x⁻¹ * ((g : G)⁻¹ * x * (g : G)⁻¹⁻¹) = x⁻¹ * (g : G)⁻¹ * x * (g : G) := by group
          rwa [e1] at this
        have h4 : x⁻¹ * (g : G)⁻¹ * x * (g : G) ∈ E ⊓ H := Subgroup.mem_inf.2 ⟨h3, h2⟩
        rw [hEH, Subgroup.mem_bot] at h4
        calc (g : G) * x = (g : G) * x * (x⁻¹ * (g : G)⁻¹ * x * (g : G)) := by rw [h4, mul_one]
          _ = x * (g : G) := by group
      exact hD.cent_H hgH (hcomm e hEe) (hcomm e₁ hEe₁)
    · intro hg a
      obtain ⟨n, hn, e₀, he₀, hae⟩ := hdec a a.2
      have hgi : (g : G)⁻¹ ∈ zpowers (h ^ 3) := inv_mem hg
      have hnc : n⁻¹ * (g : G)⁻¹ * n ∈ zpowers (h ^ 3) := by
        have := (Subgroup.mem_normalizer_iff.1 (hD.H_normalizes_h3 (inv_mem hn)) (g : G)⁻¹).1 hgi
        simpa using this
      have hcc : e₀⁻¹ * (n⁻¹ * (g : G)⁻¹ * n) * e₀ = n⁻¹ * (g : G)⁻¹ * n := by
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hnc
        have h1 : Commute (h ^ 3) e₀ := hD.h3_cent he₀
        have h2 : Commute ((h ^ 3) ^ j) e₀ := h1.zpow_left j
        rw [← hj]
        calc e₀⁻¹ * (h ^ 3) ^ j * e₀ = e₀⁻¹ * ((h ^ 3) ^ j * e₀) := by group
          _ = e₀⁻¹ * (e₀ * (h ^ 3) ^ j) := by rw [h2.eq]
          _ = (h ^ 3) ^ j := by group
      have hform : (a : G)⁻¹ * (g : G)⁻¹ * (a : G) = e₀⁻¹ * (n⁻¹ * (g : G)⁻¹ * n) * e₀ := by
        rw [hae]
        group
      rw [hform, hcc]
      exact h3_le_H (h := h) (t := t) hnc
  have hkereq : (MulAction.toPermHom ↥Sg (↥Sg ⧸ H.subgroupOf Sg)).ker =
      (zpowers (h ^ 3)).subgroupOf Sg := by
    ext g
    rw [hker g, Subgroup.mem_subgroupOf]
  have hNn : ((zpowers (h ^ 3)).subgroupOf Sg).Normal := by
    rw [← hkereq]
    exact MonoidHom.normal_ker _
  refine ⟨hNn, ?_⟩
  have hSgc : Nat.card Sg = 8 * 3 ^ (m + 1) := hD.card_Sg hEH
  have hHc : Nat.card (H.subgroupOf Sg) = 2 * 3 ^ (m + 1) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHSg).toEquiv]
    exact hD.card_H
  have hXc : Nat.card (↥Sg ⧸ H.subgroupOf Sg) = 4 := by
    have h1 := Subgroup.card_mul_index (H.subgroupOf Sg)
    rw [hHc, hSgc] at h1
    have h2 : (H.subgroupOf Sg).index = Nat.card (↥Sg ⧸ H.subgroupOf Sg) := rfl
    rw [h2] at h1
    have hpos : 0 < 2 * 3 ^ (m + 1) := by positivity
    have : 2 * 3 ^ (m + 1) * Nat.card (↥Sg ⧸ H.subgroupOf Sg) = 2 * 3 ^ (m + 1) * 4 := by
      rw [h1]
      ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hN₀c : Nat.card ((zpowers (h ^ 3)).subgroupOf Sg) = 3 ^ m := by
    have hle : zpowers (h ^ 3) ≤ Sg := (h3_le_H (h := h) (t := t)).trans hHSg
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact hD.card_zpowers_h3
  have hQc : Nat.card (↥Sg ⧸ (zpowers (h ^ 3)).subgroupOf Sg) = 24 := by
    have h1 := Subgroup.card_mul_index ((zpowers (h ^ 3)).subgroupOf Sg)
    rw [hN₀c, hSgc] at h1
    have h2 : ((zpowers (h ^ 3)).subgroupOf Sg).index =
        Nat.card (↥Sg ⧸ (zpowers (h ^ 3)).subgroupOf Sg) := rfl
    rw [h2] at h1
    have hpos : 0 < 3 ^ m := by positivity
    have : 3 ^ m * Nat.card (↥Sg ⧸ (zpowers (h ^ 3)).subgroupOf Sg) = 3 ^ m * 24 := by
      rw [h1, pow_succ]
      ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  let eX : (↥Sg ⧸ H.subgroupOf Sg) ≃ Fin 4 := Finite.equivFinOfCardEq hXc
  let φ : ↥Sg →* Equiv.Perm (Fin 4) :=
    (Equiv.permCongrHom eX).toMonoidHom.comp (MulAction.toPermHom ↥Sg (↥Sg ⧸ H.subgroupOf Sg))
  have hφker : φ.ker = (zpowers (h ^ 3)).subgroupOf Sg := by
    rw [← hkereq]
    ext g
    simp only [φ, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact map_eq_one_iff _ (Equiv.permCongrHom eX).injective
  have : φ.ker.Normal := MonoidHom.normal_ker φ
  have := hNn
  have hinj : Function.Injective (QuotientGroup.kerLift φ) := QuotientGroup.kerLift_injective φ
  have hcardQ : Nat.card (↥Sg ⧸ φ.ker) = 24 := by
    rw [hφker]
    exact hQc
  have hperm : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Nat.factorial]
  have hbij : Function.Bijective (QuotientGroup.kerLift φ) :=
    hinj.bijective_of_nat_card_le (by rw [hcardQ, hperm])
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hφker).symm.trans (MulEquiv.ofBijective _ hbij)⟩

end Basic

end S4Data

section Dihedral

variable {G : Type*} [Group G]

theorem zpowers_t_le_normalizer {h t : G} (ht2 : t * t = 1) (hth : t * h * t⁻¹ = h⁻¹) :
    zpowers t ≤ normalizer ((zpowers h : Subgroup G) : Set G) := by
  rw [zpowers_le]
  apply mem_normalizer_of_invol ht2
  intro p hp
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
  have h1 : t * h ^ i * t⁻¹ = (h⁻¹) ^ i := by
    have := map_zpow (MulAut.conj t) h i
    simpa [MulAut.conj_apply, hth] using this
  rw [h1]
  exact Subgroup.zpow_mem _ (inv_mem (Subgroup.mem_zpowers h)) i

end Dihedral

section Trio

variable {G : Type*} [Group G]

theorem exists_trio {E U : Subgroup G} {h t e : G} {m : ℕ}
    (hEsq : ∀ x ∈ E, x * x = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hhE : ∀ x ∈ E, h⁻¹ * x * h ∈ E) (hh3 : ∀ x ∈ E, h ^ 3 * x = x * h ^ 3)
    (hCh : ∀ x ∈ E, h * x = x * h → x = 1) (hUh : ∀ x ∈ U, h⁻¹ * x * h ∈ U)
    (hord : orderOf h = 3 ^ (m + 1)) (ht2 : t * t = 1) (hth : t * h * t⁻¹ = h⁻¹) (heE : e ∈ E)
    (heU : e ∉ U) (hte : t * e * t⁻¹ = e) :
    ∃ e₁ e₂ : G, S4Data h t e e₁ e₂ m ∧ e₁ ∈ E ∧ e₂ ∈ E ∧ (zpowers e ⊔ zpowers e₁) ⊓ U = ⊥ := by
  obtain ⟨e₁, he₁⟩ : ∃ e₁, e₁ = h⁻¹ * e * h := ⟨_, rfl⟩
  obtain ⟨e₂, he₂⟩ : ∃ e₂, e₂ = h⁻¹ * e₁ * h := ⟨_, rfl⟩
  have he₁E : e₁ ∈ E := he₁ ▸ hhE e heE
  have he₂E : e₂ ∈ E := he₂ ▸ hhE e₁ he₁E
  have e3 : h ^ 3 = h * h * h := by simp only [pow_succ, pow_zero, one_mul]
  have h3' : ∀ x ∈ E, (h * h * h) * x = x * (h * h * h) := fun x hx => by
    have := hh3 x hx
    rwa [e3] at this
  have h3x : ∀ x ∈ E, h⁻¹ * (h⁻¹ * (h⁻¹ * x * h) * h) * h = x := fun x hx => by
    calc h⁻¹ * (h⁻¹ * (h⁻¹ * x * h) * h) * h = (h * h * h)⁻¹ * (x * (h * h * h)) := by group
      _ = (h * h * h)⁻¹ * ((h * h * h) * x) := by rw [h3' x hx]
      _ = x := by group
  have hh₂ : h⁻¹ * e₂ * h = e := by
    rw [he₂, he₁]
    exact h3x e heE
  have hconj_e : h * e * h⁻¹ = e₂ := by
    calc h * e * h⁻¹ = h⁻¹ * h⁻¹ * ((h * h * h) * e) * h⁻¹ := by group
      _ = h⁻¹ * h⁻¹ * (e * (h * h * h)) * h⁻¹ := by rw [h3' e heE]
      _ = h⁻¹ * (h⁻¹ * e * h) * h := by group
      _ = e₂ := by rw [he₂, he₁]
  have he₁' : h * e₁ * h⁻¹ = e := by rw [he₁]; group
  have he₂' : h * e₂ * h⁻¹ = e₁ := by rw [he₂]; group
  have hcomm_h : ∀ x : G, h⁻¹ * x * h = x → h * x = x * h := fun x hx => by
    calc h * x = h * (h⁻¹ * x * h) := by rw [hx]
      _ = x * h := by group
  have ne₀ : e ≠ 1 := fun h1 => heU (h1 ▸ one_mem U)
  have ne₁ : e₁ ≠ 1 := by
    intro h1
    apply ne₀
    rw [← he₁']
    rw [h1]
    group
  have ne₂ : e₂ ≠ 1 := by
    intro h1
    apply ne₁
    rw [← he₂', h1]
    group
  have n₀₁ : e ≠ e₁ := by
    intro h1
    apply ne₀
    apply hCh e heE
    apply hcomm_h
    rw [← he₁]
    exact h1.symm
  have n₁₂ : e₁ ≠ e₂ := by
    intro h1
    apply ne₁
    apply hCh e₁ he₁E
    apply hcomm_h
    rw [← he₂]
    exact h1.symm
  have n₀₂ : e ≠ e₂ := by
    intro h1
    apply ne₀
    have hc2 : (h * h) * e = e * (h * h) := by
      have h2 : e = h⁻¹ * (h⁻¹ * e * h) * h := by rw [← he₁, ← he₂]; exact h1
      calc (h * h) * e = (h * h) * (h⁻¹ * (h⁻¹ * e * h) * h) := by rw [← h2]
        _ = e * (h * h) := by group
    have h4 : (h * e) * (h * h) = (e * h) * (h * h) := by
      calc (h * e) * (h * h) = h * (e * (h * h)) := by group
        _ = h * ((h * h) * e) := by rw [hc2]
        _ = (h * h * h) * e := by group
        _ = e * (h * h * h) := h3' e heE
        _ = (e * h) * (h * h) := by group
    exact hCh e heE (mul_right_cancel h4)
  have hprod : e * e₁ * e₂ = 1 := by
    have hpE : e * e₁ * e₂ ∈ E := mul_mem (mul_mem heE he₁E) he₂E
    have h1 : h⁻¹ * (e * e₁ * e₂) * h = e * e₁ * e₂ := by
      calc h⁻¹ * (e * e₁ * e₂) * h = (h⁻¹ * e * h) * (h⁻¹ * e₁ * h) * (h⁻¹ * e₂ * h) := by group
        _ = e₁ * e₂ * e := by rw [← he₁, ← he₂, hh₂]
        _ = e * (e₁ * e₂) := hEc _ (mul_mem he₁E he₂E) e heE
        _ = e * e₁ * e₂ := by group
    exact hCh _ hpE (hcomm_h _ h1)
  have htinv : t * h⁻¹ * t⁻¹ = h := by
    calc t * h⁻¹ * t⁻¹ = (t * h * t⁻¹)⁻¹ := by group
      _ = h := by rw [hth, inv_inv]
  have ht₁ : t * e₁ * t⁻¹ = e₂ := by
    calc t * e₁ * t⁻¹ = (t * h⁻¹ * t⁻¹) * (t * e * t⁻¹) * (t * h * t⁻¹) := by rw [he₁]; group
      _ = h * e * h⁻¹ := by rw [htinv, hte, hth]
      _ = e₂ := hconj_e
  have ht₂ : t * e₂ * t⁻¹ = e₁ := by
    calc t * e₂ * t⁻¹ = (t * h⁻¹ * t⁻¹) * (t * e₁ * t⁻¹) * (t * h * t⁻¹) := by rw [he₂]; group
      _ = h * e₂ * h⁻¹ := by rw [htinv, ht₁, hth]
      _ = e₁ := he₂'
  have hD : S4Data h t e e₁ e₂ m :=
    { hord := hord
      ht2 := ht2
      hth := hth
      he2 := hEsq e heE
      he₁2 := hEsq e₁ he₁E
      he₂2 := hEsq e₂ he₂E
      c₁ := hEc e heE e₁ he₁E
      c₂ := hEc e heE e₂ he₂E
      c₃ := hEc e₁ he₁E e₂ he₂E
      prod := hprod
      hh₀ := he₁.symm
      hh₁ := he₂.symm
      hh₂ := hh₂
      ht₀ := hte
      ht₁ := ht₁
      ht₂ := ht₂
      ne₀ := ne₀
      ne₁ := ne₁
      ne₂ := ne₂
      n₀₁ := n₀₁
      n₀₂ := n₀₂
      n₁₂ := n₁₂ }
  refine ⟨e₁, e₂, hD, he₁E, he₂E, ?_⟩
  rw [eq_bot_iff]
  intro x hx
  rcases (hD.mem_E₀).1 hx.1 with h1 | h1 | h1 | h1
  · rw [h1]
    exact one_mem _
  · exact absurd (h1 ▸ hx.2) heU
  · exfalso
    have hx2 : e₁ ∈ U := h1 ▸ hx.2
    have h2 : e₂ ∈ U := he₂ ▸ hUh e₁ hx2
    exact heU (hh₂ ▸ hUh e₂ h2)
  · exfalso
    have hx2 : e₂ ∈ U := h1 ▸ hx.2
    exact heU (hh₂ ▸ hUh e₂ hx2)

end Trio

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
