module

public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.SecTwoDefs

public section
namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open

variable {X : Type*} [Group X]

section Sylow

variable [Finite X]

@[expose] noncomputable def secTwoSylowOf {p : ℕ} [Fact p.Prime] {H R : Subgroup X}
    (hR : fusionIsSylowIn p R H) : Sylow p H where
  toSubgroup := R.subgroupOf H
  isPGroup' := hR.2.1.comap_of_injective H.subtype H.subtype_injective
  is_maximal' {Q} hQ hle := by
    have hQ' : IsPGroup p (Q.map H.subtype) := hQ.map H.subtype
    have hRQ : R ≤ Q.map H.subtype := fun x hx => ⟨⟨x, hR.1 hx⟩, hle hx, rfl⟩
    have heq := hR.2.2 _ (Subgroup.map_subtype_le Q) hQ' hRQ
    apply le_antisymm _ hle
    intro q hq
    have : (q : X) ∈ R := by rw [← heq]; exact ⟨q, hq, rfl⟩
    exact this

theorem secTwo_exists_conj_le {p : ℕ} [Fact p.Prime] {H R P : Subgroup X}
    (hR : fusionIsSylowIn p R H) (hPH : P ≤ H) (hP : IsPGroup p P) :
    ∃ c ∈ H, ∀ x ∈ P, c * x * c⁻¹ ∈ R := by
  obtain ⟨T, hT⟩ := (hP.comap_of_injective H.subtype H.subtype_injective).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H T (secTwoSylowOf hR)
  refine ⟨c, c.2, fun x hx => ?_⟩
  have hxT : (⟨x, hPH hx⟩ : H) ∈ (T : Subgroup H) := hT hx
  have h1 : c * ⟨x, hPH hx⟩ * c⁻¹ ∈ ((c • T : Sylow p H) : Subgroup H) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [MulAut.inv_def, MulAut.conj_symm_apply, mul_assoc] using hxT
  rw [hc] at h1
  exact h1

theorem secTwo_exists_mem_normalizer {H P : Subgroup X} (hP : IsPGroup 2 P) (hHP : H ≤ P)
    (hne : H ≠ P) : ∃ s ∈ P, s ∉ H ∧ s ∈ normalizer (H : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt : H.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne (le_antisymm hHP fun x hx => ?_)
    have : (⟨x, hx⟩ : P) ∈ H.subgroupOf P := htop ▸ Subgroup.mem_top _
    exact this
  obtain ⟨s, hs, hsH⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  refine ⟨s, s.2, hsH, ?_⟩
  rw [mem_normalizer_iff]
  intro x
  by_cases hx : x ∈ P
  · have := (mem_normalizer_iff.mp hs) ⟨x, hx⟩
    exact this
  · constructor
    · intro hxH; exact absurd (hHP hxH) hx
    · intro hxH
      exfalso; apply hx
      have h1 : (s : X) * x * (s : X)⁻¹ ∈ P := hHP hxH
      have : x = (s : X)⁻¹ * ((s : X) * x * (s : X)⁻¹) * s := by group
      rw [this]
      exact mul_mem (mul_mem (inv_mem s.2) h1) s.2

end Sylow

variable {t u : X}

namespace SecTwoHyp

variable (h : SecTwoHyp X t u)
include h

theorem t_sq : t ^ 2 = 1 := by rw [← h.orderOf_t]; exact pow_orderOf_eq_one t

theorem t_mul_t : t * t = 1 := by rw [← sq]; exact h.t_sq

theorem t_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t

theorem t_ne_one : t ≠ 1 := by
  intro ht; have := h.orderOf_t; rw [ht, orderOf_one] at this; omega

theorem u_pow_four : u ^ 4 = 1 := by rw [← h.orderOf_u]; exact pow_orderOf_eq_one u

theorem z_sq : (u ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact h.u_pow_four

theorem z_ne_one : u ^ 2 ≠ 1 := by
  intro hz
  have h1 := orderOf_dvd_of_pow_eq_one hz
  rw [h.orderOf_u] at h1
  omega

theorem z_inv : (u ^ 2)⁻¹ = u ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h.z_sq)

theorem commute_tu : Commute t u := h.commute

omit h in
theorem t_mem_R : t ∈ secTwoR t u := subset_closure (by simp)

omit h in
theorem u_mem_R : u ∈ secTwoR t u := subset_closure (by simp)

theorem exists_pow_of_mem_R {r : X} (hr : r ∈ secTwoR t u) : ∃ a b : ℕ, r = t ^ a * u ^ b := by
  induction hr using Subgroup.closure_induction_left with
  | one => exact ⟨0, 0, by simp⟩
  | mul_left x hx y hy ih =>
    obtain ⟨a, b, rfl⟩ := ih
    rcases hx with rfl | rfl
    · exact ⟨a + 1, b, by rw [pow_succ', mul_assoc]⟩
    · refine ⟨a, b + 1, ?_⟩
      rw [pow_succ', ← mul_assoc, ← mul_assoc, ((h.commute_tu).pow_left a).eq]
  | inv_mul_cancel x hx y hy ih =>
    obtain ⟨a, b, rfl⟩ := ih
    rcases hx with rfl | rfl
    · exact ⟨a + 1, b, by rw [h.t_inv, pow_succ', mul_assoc]⟩
    · refine ⟨a, b + 3, ?_⟩
      have hu : x⁻¹ = x ^ 3 := by
        rw [inv_eq_iff_mul_eq_one, ← pow_succ', h.u_pow_four]
      rw [hu, ← mul_assoc, (((h.commute_tu).pow_left a).pow_right 3).eq.symm, mul_assoc,
        ← pow_add, add_comm 3 b]

theorem orderOf_z : orderOf (u ^ 2) = 2 := orderOf_eq_prime h.z_sq h.z_ne_one

theorem mul_comm_of_mem_R {r s : X} (hr : r ∈ secTwoR t u) (hs : s ∈ secTwoR t u) :
    r * s = s * r := by
  obtain ⟨a, b, rfl⟩ := h.exists_pow_of_mem_R hr
  obtain ⟨c, d, rfl⟩ := h.exists_pow_of_mem_R hs
  have h1 := (h.commute_tu.pow_left a).pow_right d
  have h2 := (h.commute_tu.pow_left c).pow_right b
  have e1 : t ^ a * u ^ b * (t ^ c * u ^ d) = t ^ (a + c) * u ^ (b + d) := by
    calc t ^ a * u ^ b * (t ^ c * u ^ d) = t ^ a * (u ^ b * t ^ c) * u ^ d := by group
      _ = t ^ a * (t ^ c * u ^ b) * u ^ d := by rw [← h2.eq]
      _ = t ^ (a + c) * u ^ (b + d) := by rw [pow_add, pow_add]; group
  have e2 : t ^ c * u ^ d * (t ^ a * u ^ b) = t ^ (c + a) * u ^ (d + b) := by
    calc t ^ c * u ^ d * (t ^ a * u ^ b) = t ^ c * (u ^ d * t ^ a) * u ^ b := by group
      _ = t ^ c * (t ^ a * u ^ d) * u ^ b := by rw [← h1.eq]
      _ = t ^ (c + a) * u ^ (d + b) := by rw [pow_add, pow_add]; group
  rw [e1, e2, add_comm a c, add_comm b d]

theorem sq_of_mem_R {r : X} (hr : r ∈ secTwoR t u) : r ^ 2 = 1 ∨ r ^ 2 = u ^ 2 := by
  obtain ⟨a, b, rfl⟩ := h.exists_pow_of_mem_R hr
  have hc := (h.commute_tu.pow_left a).pow_right b
  rw [hc.mul_pow, ← pow_mul, ← pow_mul, mul_comm a 2, pow_mul, h.t_sq, one_pow, one_mul,
    mul_comm b 2, pow_mul, ← pow_mod_orderOf (u ^ 2) b, h.orderOf_z]
  rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> rw [hb] <;> simp

theorem eq_of_mem_R_of_sq_eq_one {r : X} (hr : r ∈ secTwoR t u) (hr2 : r ^ 2 = 1) :
    r = 1 ∨ r = t ∨ r = u ^ 2 ∨ r = t * u ^ 2 := by
  obtain ⟨a, b, rfl⟩ := h.exists_pow_of_mem_R hr
  rw [← pow_mod_orderOf t a, h.orderOf_t, ← pow_mod_orderOf u b, h.orderOf_u] at hr2 ⊢
  have hc := (h.commute_tu.pow_left (a % 2)).pow_right (b % 4)
  rw [hc.mul_pow, ← pow_mul, ← pow_mul, mul_comm (a % 2) 2, pow_mul, h.t_sq, one_pow,
    one_mul] at hr2
  have ha : a % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hb : b % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases (a % 2) <;> interval_cases (b % 4)
  · simp
  · exfalso; apply h.z_ne_one; simpa using hr2
  · simp
  · exfalso; apply h.z_ne_one
    rw [show (3 : ℕ) * 2 = 4 + 2 from rfl, pow_add, h.u_pow_four, one_mul] at hr2
    exact hr2
  · simp
  · exfalso; apply h.z_ne_one; simpa using hr2
  · simp
  · exfalso; apply h.z_ne_one
    rw [show (3 : ℕ) * 2 = 4 + 2 from rfl, pow_add, h.u_pow_four, one_mul] at hr2
    exact hr2

theorem R_le_centralizer : secTwoR t u ≤ centralizer ({t} : Set X) := h.sylow.1

theorem isPGroup_R : IsPGroup 2 (secTwoR t u) := h.sylow.2.1

theorem eq_R_of_le {P : Subgroup X} (hP : P ≤ centralizer ({t} : Set X)) (hP2 : IsPGroup 2 P)
    (hRP : secTwoR t u ≤ P) : P = secTwoR t u :=
  h.sylow.2.2 P hP hP2 hRP

theorem commute_t_of_mem_R {r : X} (hr : r ∈ secTwoR t u) : r * t = t * r :=
  mem_centralizer_singleton_iff.mp (h.R_le_centralizer hr)

theorem le_R_of_normalized {N : Subgroup X} (hN : N ≤ centralizer ({t} : Set X))
    (hN2 : IsPGroup 2 N) (hnorm : ∀ c ∈ centralizer ({t} : Set X), ∀ n ∈ N, c * n * c⁻¹ ∈ N) :
    N ≤ secTwoR t u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRN : secTwoR t u ≤ normalizer (N : Set X) := by
    intro r hr
    rw [mem_normalizer_iff]
    intro n
    constructor
    · exact hnorm r (h.R_le_centralizer hr) n
    · intro hn
      have := hnorm r⁻¹ (inv_mem (h.R_le_centralizer hr)) _ hn
      simpa [mul_assoc] using this
  have hsup := hN2.to_sup_of_normal_left' h.isPGroup_R hRN
  have heq := h.eq_R_of_le (sup_le hN h.R_le_centralizer) hsup le_sup_right
  rw [← heq]
  exact le_sup_left

variable [Finite X]

theorem sq_ne_t (g : X) : g ^ 2 ≠ t := by
  intro hg
  have hgt : g ∈ centralizer ({t} : Set X) := by
    rw [mem_centralizer_singleton_iff, ← hg, ← pow_succ', ← pow_succ]
  have hg4 : g ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hg, h.t_sq]
  have hP : IsPGroup 2 (zpowers g) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    have hd : orderOf g ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one hg4
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    exact ⟨k, hk⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc, hcR⟩ := secTwo_exists_conj_le h.sylow (zpowers_le.mpr hgt) hP
  have hmem := hcR g (mem_zpowers g)
  have hct : c * t * c⁻¹ = t := by
    rw [mem_centralizer_singleton_iff] at hc
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  have hsq : (c * g * c⁻¹) ^ 2 = c * g ^ 2 * c⁻¹ := by rw [conj_pow]
  rcases h.sq_of_mem_R hmem with h1 | h1
  · apply h.t_ne_one
    rw [← hct, ← hg, ← hsq, h1]
  · apply h.sq_ne
    rw [← h1, hsq, hg, hct]

theorem conj_z_ne_t (g : X) : g * u ^ 2 * g⁻¹ ≠ t := by
  rw [← conj_pow]
  exact h.sq_ne_t _

omit h [Finite X] in
theorem isPGroup_of_sq_eq_one {E : Subgroup X} (hE : ∀ e ∈ E, e ^ 2 = 1) : IsPGroup 2 E := by
  intro e
  refine ⟨1, ?_⟩
  rw [pow_one, Subtype.ext_iff, Subgroup.coe_pow, Subgroup.coe_one]
  exact hE e e.2

omit h [Finite X] in
theorem mul_comm_of_sq_eq_one {E : Subgroup X} (hE : ∀ e ∈ E, e ^ 2 = 1) {a b : X} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := by
  have h1 : a * a = 1 := by rw [← sq]; exact hE a ha
  have h2 : b * b = 1 := by rw [← sq]; exact hE b hb
  have h3 : a * b * (a * b) = 1 := by rw [← sq]; exact hE _ (mul_mem ha hb)
  calc a * b = a * b * (a * b) * (b * a) := by
        rw [show a * b * (a * b) * (b * a) = a * b * a * (b * b) * a by group, h2, mul_one,
          mul_assoc, mul_assoc, h1, mul_one]
    _ = b * a := by rw [h3, one_mul]

theorem card_le_four_of_le_centralizer {E : Subgroup X} (hE : ∀ e ∈ E, e ^ 2 = 1)
    (hEt : E ≤ centralizer ({t} : Set X)) : Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, -, hcR⟩ := secTwo_exists_conj_le h.sylow hEt (isPGroup_of_sq_eq_one hE)
  classical
  let F : Finset X := {1, t, u ^ 2, t * u ^ 2}
  have hmap : ∀ e : E, c * (e : X) * c⁻¹ ∈ F := by
    intro e
    have hsq : (c * (e : X) * c⁻¹) ^ 2 = 1 := by rw [conj_pow, hE e e.2]; group
    rcases h.eq_of_mem_R_of_sq_eq_one (hcR e e.2) hsq with h1 | h1 | h1 | h1 <;>
      simp [F, h1]
  have hinj : Function.Injective (fun e : E => (⟨c * (e : X) * c⁻¹, hmap e⟩ : F)) := by
    intro a b hab
    apply Subtype.ext
    simpa using congrArg Subtype.val hab
  calc Nat.card E ≤ Nat.card F := Nat.card_le_card_of_injective _ hinj
    _ = F.card := Nat.card_eq_finsetCard F
    _ ≤ 4 := Finset.card_le_four

theorem card_le_four {E : Subgroup X} (hE : ∀ e ∈ E, e ^ 2 = 1)
    (htE : ∀ e ∈ E, t * e * t⁻¹ ∈ E) : Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases htmem : t ∈ E
  · refine h.card_le_four_of_le_centralizer hE fun e he => ?_
    rw [mem_centralizer_singleton_iff]
    exact mul_comm_of_sq_eq_one hE he htmem
  let E₀ : Subgroup X := E ⊓ centralizer ({t} : Set X)
  have hE₀ : ∀ e ∈ E₀, e ^ 2 = 1 := fun e he => hE e he.1
  have hE₀card : Nat.card E₀ ≤ 2 := by
    obtain ⟨c, hc, hcR⟩ := secTwo_exists_conj_le h.sylow (inf_le_right : E₀ ≤ _)
      (isPGroup_of_sq_eq_one hE₀)
    have hct : c * t * c⁻¹ = t := by
      rw [mem_centralizer_singleton_iff] at hc
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    have hcases : ∀ e ∈ E₀, c * e * c⁻¹ = 1 ∨ c * e * c⁻¹ = u ^ 2 ∨
        c * e * c⁻¹ = t * u ^ 2 := by
      intro e he
      have hsq : (c * e * c⁻¹) ^ 2 = 1 := by rw [conj_pow, hE₀ e he]; group
      rcases h.eq_of_mem_R_of_sq_eq_one (hcR e he) hsq with h1 | h1 | h1 | h1
      · exact Or.inl h1
      · exfalso; apply htmem
        have : e = t := by
          calc e = c⁻¹ * (c * e * c⁻¹) * c := by group
            _ = c⁻¹ * (c * t * c⁻¹) * c := by rw [h1, hct]
            _ = t := by group
        exact this ▸ he.1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
    classical
    by_cases hz : ∃ e ∈ E₀, c * e * c⁻¹ = u ^ 2
    · obtain ⟨e₁, he₁, he₁z⟩ := hz
      let F : Finset X := {1, u ^ 2}
      have hmap : ∀ e : E₀, c * (e : X) * c⁻¹ ∈ F := by
        intro e
        rcases hcases e e.2 with h1 | h1 | h1
        · simp [F, h1]
        · simp [F, h1]
        · exfalso; apply htmem
          have hprod : c * ((e : X) * e₁) * c⁻¹ = t := by
            rw [show c * ((e : X) * e₁) * c⁻¹ = (c * e * c⁻¹) * (c * e₁ * c⁻¹) by group, h1,
              he₁z, mul_assoc, ← sq, h.z_sq, mul_one]
          have : (e : X) * e₁ = t := by
            calc (e : X) * e₁ = c⁻¹ * (c * ((e : X) * e₁) * c⁻¹) * c := by group
              _ = c⁻¹ * (c * t * c⁻¹) * c := by rw [hprod, hct]
              _ = t := by group
          exact this ▸ (mul_mem e.2 he₁).1
      have hinj : Function.Injective
          (fun e : E₀ => (⟨c * (e : X) * c⁻¹, hmap e⟩ : F)) := by
        intro a b hab
        apply Subtype.ext
        simpa using congrArg Subtype.val hab
      calc Nat.card E₀ ≤ Nat.card F := Nat.card_le_card_of_injective _ hinj
        _ = F.card := Nat.card_eq_finsetCard F
        _ ≤ 2 := Finset.card_le_two
    · push Not at hz
      let F : Finset X := {1, t * u ^ 2}
      have hmap : ∀ e : E₀, c * (e : X) * c⁻¹ ∈ F := by
        intro e
        rcases hcases e e.2 with h1 | h1 | h1
        · simp [F, h1]
        · exact absurd h1 (hz e e.2)
        · simp [F, h1]
      have hinj : Function.Injective
          (fun e : E₀ => (⟨c * (e : X) * c⁻¹, hmap e⟩ : F)) := by
        intro a b hab
        apply Subtype.ext
        simpa using congrArg Subtype.val hab
      calc Nat.card E₀ ≤ Nat.card F := Nat.card_le_card_of_injective _ hinj
        _ = F.card := Nat.card_eq_finsetCard F
        _ ≤ 2 := Finset.card_le_two
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    mul_comm_of_sq_eq_one hE ha hb
  let φ : E →* E :=
    { toFun := fun e => ⟨e * (t * e * t⁻¹), mul_mem e.2 (htE e e.2)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        change (a : X) * b * (t * (a * b) * t⁻¹) = a * (t * a * t⁻¹) * (b * (t * b * t⁻¹))
        have h1 := hcomm b b.2 _ (htE a a.2)
        calc (a : X) * b * (t * (a * b) * t⁻¹) = a * (b * (t * a * t⁻¹)) * (t * b * t⁻¹) := by
              group
          _ = a * ((t * a * t⁻¹) * b) * (t * b * t⁻¹) := by rw [h1]
          _ = a * (t * a * t⁻¹) * (b * (t * b * t⁻¹)) := by group }
  have hker : ∀ e : E, e ∈ φ.ker → (e : X) ∈ E₀ := by
    intro e he
    have h1 : (e : X) * (t * e * t⁻¹) = 1 := congrArg Subtype.val he
    refine Subgroup.mem_inf.mpr ⟨e.2, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have he2 : (e : X)⁻¹ = e := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hE e e.2)
    have h2 : t * e * t⁻¹ = (e : X) := by
      rw [eq_inv_of_mul_eq_one_right h1, he2]
    calc (e : X) * t = t * e * t⁻¹ * t := by rw [h2]
      _ = t * e := by group
  have hrange : ∀ e : E, e ∈ φ.range → (e : X) ∈ E₀ := by
    rintro e ⟨a, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨(φ a).2, ?_⟩
    rw [mem_centralizer_singleton_iff]
    change (a : X) * (t * a * t⁻¹) * t = t * ((a : X) * (t * a * t⁻¹))
    have h1 := hcomm _ (htE a a.2) a a.2
    rw [h.t_inv] at h1 ⊢
    calc (a : X) * (t * a * t) * t = a * t * a * (t * t) := by group
      _ = t * t * (a * t * a) := by rw [h.t_mul_t, mul_one, one_mul]
      _ = t * ((t * a * t) * a) := by group
      _ = t * ((a : X) * (t * a * t)) := by rw [h1]
  have hk : Nat.card φ.ker ≤ Nat.card E₀ :=
    Nat.card_le_card_of_injective (fun e : φ.ker => (⟨e.1, hker e.1 e.2⟩ : E₀))
      (fun a b hab => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hab)))
  have hr : Nat.card φ.range ≤ Nat.card E₀ :=
    Nat.card_le_card_of_injective (fun e : φ.range => (⟨e.1, hrange e.1 e.2⟩ : E₀))
      (fun a b hab => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hab)))
  rw [← Subgroup.card_ker_mul_card_range φ]
  calc Nat.card φ.ker * Nat.card φ.range ≤ 2 * 2 :=
        Nat.mul_le_mul (hk.trans hE₀card) (hr.trans hE₀card)
    _ = 4 := rfl

omit [Finite X] in
theorem exists_sylow_ge : ∃ S : Sylow 2 X, secTwoR t u ≤ (S : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact h.isPGroup_R.exists_le_sylow

omit [Finite X] in
theorem inf_centralizer_eq {S : Subgroup X} (hS : IsPGroup 2 S) (hRS : secTwoR t u ≤ S) :
    S ⊓ centralizer ({t} : Set X) = secTwoR t u :=
  h.eq_R_of_le inf_le_right hS.to_inf_left (le_inf hRS h.R_le_centralizer)

omit [Finite X] in
theorem mem_R_of_commute {S : Subgroup X} (hS : IsPGroup 2 S) (hRS : secTwoR t u ≤ S) {s : X}
    (hs : s ∈ S) (hst : s * t = t * s) : s ∈ secTwoR t u := by
  rw [← h.inf_centralizer_eq hS hRS]
  exact ⟨hs, mem_centralizer_singleton_iff.mpr hst⟩

theorem exists_conj_t_eq {S : Subgroup X} (hS : IsPGroup 2 S) (hRS : secTwoR t u ≤ S)
    (hne : secTwoR t u ≠ S) :
    ∃ s ∈ S, s ∉ secTwoR t u ∧ s ∈ normalizer (secTwoR t u : Set X) ∧
      s * t * s⁻¹ = t * u ^ 2 := by
  obtain ⟨s, hsS, hsR, hsN⟩ := secTwo_exists_mem_normalizer hS hRS hne
  refine ⟨s, hsS, hsR, hsN, ?_⟩
  have hmem : s * t * s⁻¹ ∈ secTwoR t u := (mem_normalizer_iff.mp hsN t).mp t_mem_R
  have hsq : (s * t * s⁻¹) ^ 2 = 1 := by rw [conj_pow, h.t_sq]; group
  rcases h.eq_of_mem_R_of_sq_eq_one hmem hsq with h1 | h1 | h1 | h1
  · exfalso; apply h.t_ne_one
    calc t = s⁻¹ * (s * t * s⁻¹) * s := by group
      _ = 1 := by rw [h1]; group
  · exfalso; apply hsR
    apply h.mem_R_of_commute hS hRS hsS
    calc s * t = s * t * s⁻¹ * s := by group
      _ = t * s := by rw [h1]
  · exfalso
    apply h.conj_z_ne_t s⁻¹
    rw [← h1]; group
  · exact h1

theorem z_mem_center {S : Subgroup X} (hS : IsPGroup 2 S) (hRS : secTwoR t u ≤ S) {s : X}
    (hs : s ∈ S) : s * u ^ 2 = u ^ 2 * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hRS' : secTwoR t u = S
  · subst hRS'
    exact h.mul_comm_of_mem_R hs (pow_mem u_mem_R 2)
  obtain ⟨s₀, hs₀S, -, -, hs₀t⟩ := h.exists_conj_t_eq hS hRS hRS'
  have : Nontrivial S := ⟨⟨1, ⟨t, hRS t_mem_R⟩, fun h1 => h.t_ne_one
    (congrArg Subtype.val h1).symm⟩⟩
  have hZ2 : IsPGroup 2 (center S) := hS.to_subgroup _
  have : Nontrivial (center S) := hS.center_nontrivial
  obtain ⟨n, hn, hcard⟩ := hZ2.nontrivial_iff_card.mp inferInstance
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := center S) 2 (by
    rw [hcard]; exact dvd_pow_self 2 (by omega))
  have hcX : orderOf ((c : S) : X) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  have hcS : ((c : S) : X) ∈ S := (c : S).2
  have hcomm : ∀ g ∈ S, g * ((c : S) : X) = ((c : S) : X) * g := fun g hg =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨g, hg⟩)
  have hcR : ((c : S) : X) ∈ secTwoR t u :=
    h.mem_R_of_commute hS hRS hcS (hcomm t (hRS t_mem_R)).symm
  have hc2 : ((c : S) : X) ^ 2 = 1 := by rw [← hcX]; exact pow_orderOf_eq_one _
  have hcz : ((c : S) : X) = u ^ 2 := by
    rcases h.eq_of_mem_R_of_sq_eq_one hcR hc2 with h1 | h1 | h1 | h1
    · rw [h1, orderOf_one] at hcX; omega
    · exfalso; apply hRS'
      refine le_antisymm hRS fun g hg => h.mem_R_of_commute hS hRS hg ?_
      rw [← h1]; exact hcomm g hg
    · exact h1
    · exfalso; apply h.z_ne_one
      have e1 : s₀ * (t * u ^ 2) * s₀⁻¹ = t * u ^ 2 := by
        rw [← h1, hcomm s₀ hs₀S]; group
      have e2 : s₀ * u ^ 2 * s₀⁻¹ = 1 := by
        calc s₀ * u ^ 2 * s₀⁻¹ = (s₀ * t * s₀⁻¹)⁻¹ * (s₀ * (t * u ^ 2) * s₀⁻¹) := by group
          _ = 1 := by rw [hs₀t, e1]; group
      calc u ^ 2 = s₀⁻¹ * (s₀ * u ^ 2 * s₀⁻¹) * s₀ := by group
        _ = 1 := by rw [e2]; group
  rw [← hcz]
  exact hcomm s hs

end SecTwoHyp

end CFSG.LocalAnalysis.EvenBN.Tits
