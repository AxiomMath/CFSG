module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherShapeExclusionTools
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Basic

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.ShapeExclusion

open Subgroup

variable {G : Type*} [Group G]

structure Config (S : Subgroup G) (t x ρ : G) (k : ℕ) : Prop where
  hk : 2 ≤ k
  t_sq : t ^ 2 = 1
  t_norm : t ∈ normalizer (S : Set G)
  x_mem : x ∈ S
  x_order : orderOf x = 4
  x_comm : x * t = t * x
  cent : ∀ s ∈ S, s * t = t * s → s ∈ zpowers x
  rho_mem : ρ ∈ S
  t_rho : t * ρ * t⁻¹ = ρ⁻¹
  rho_x : ρ * x = x * ρ
  rho_order : orderOf ρ = 2 ^ k
  rho_pow : ρ ^ 2 ^ (k - 1) = x ^ 2
  card : Nat.card S = 2 ^ (k + 2)

namespace Config

variable {S : Subgroup G} {t x ρ : G} {k : ℕ}

theorem t_inv (h : Config S t x ρ k) : t⁻¹ = t := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two, h.t_sq]

theorem x_pow_four (h : Config S t x ρ k) : x ^ 4 = 1 := by
  rw [← h.x_order]; exact pow_orderOf_eq_one x

theorem x_sq_ne_one (h : Config S t x ρ k) : x ^ 2 ≠ 1 := by
  intro h2
  have := orderOf_dvd_of_pow_eq_one h2
  rw [h.x_order] at this
  norm_num at this

theorem t_zpow (h : Config S t x ρ k) (i : ℤ) : t * ρ ^ i * t⁻¹ = ρ ^ (-i) := by
  rw [← _root_.conj_zpow, h.t_rho, inv_zpow']

theorem x_comm_zpow (h : Config S t x ρ k) (i : ℤ) : ρ ^ i * x = x * ρ ^ i :=
  (Commute.zpow_left h.rho_x i).eq

theorem t_x (h : Config S t x ρ k) : t * x * t⁻¹ = x := by
  rw [← h.x_comm, mul_inv_cancel_right]

theorem x_not_mem (h : Config S t x ρ k) : x ∉ zpowers ρ := by
  intro hx
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hx
  have h1 := h.t_zpow i
  rw [h.t_x, zpow_neg] at h1
  apply h.x_sq_ne_one
  rw [pow_two]
  nth_rewrite 1 [h1]
  exact inv_mul_cancel _

theorem x_mem_normalizer (h : Config S t x ρ k) : x ∈ normalizer (zpowers ρ : Set G) := by
  refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun w hw => ?_)
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hw
  exact h.x_comm_zpow i

theorem x_sq_mem (h : Config S t x ρ k) : x ^ 2 ∈ zpowers ρ := by
  rw [← h.rho_pow]
  exact pow_mem (mem_zpowers ρ) _

theorem mem_M (h : Config S t x ρ k) {g : G} :
    g ∈ zpowers ρ ⊔ zpowers x ↔ g ∈ zpowers ρ ∨ x⁻¹ * g ∈ zpowers ρ :=
  Lemma37.mem_sup_zpowers_iff h.x_mem_normalizer h.x_sq_mem

theorem M_cases (h : Config S t x ρ k) {g : G} (hg : g ∈ zpowers ρ ⊔ zpowers x) :
    ∃ i : ℤ, g = ρ ^ i ∨ g = x * ρ ^ i := by
  rcases h.mem_M.1 hg with h1 | h1
  · obtain ⟨i, hi⟩ := mem_zpowers_iff.1 h1
    exact ⟨i, Or.inl hi.symm⟩
  · obtain ⟨i, hi⟩ := mem_zpowers_iff.1 h1
    exact ⟨i, Or.inr (by rw [hi]; group)⟩

theorem M_le (h : Config S t x ρ k) : zpowers ρ ⊔ zpowers x ≤ S :=
  sup_le (zpowers_le.2 h.rho_mem) (zpowers_le.2 h.x_mem)

theorem card_M [Finite G] (h : Config S t x ρ k) :
    Nat.card (zpowers ρ ⊔ zpowers x : Subgroup G) = 2 ^ (k + 1) := by
  rw [Lemma37.card_sup_zpowers h.x_mem_normalizer h.x_sq_mem h.x_not_mem, Nat.card_zpowers,
    h.rho_order, pow_succ, mul_comm]

theorem card_S_eq [Finite G] (h : Config S t x ρ k) :
    Nat.card S = 2 * Nat.card (zpowers ρ ⊔ zpowers x : Subgroup G) := by
  rw [h.card, h.card_M, pow_succ, mul_comm]

theorem M_comm (h : Config S t x ρ k) {g₁ g₂ : G} (h₁ : g₁ ∈ zpowers ρ ⊔ zpowers x)
    (h₂ : g₂ ∈ zpowers ρ ⊔ zpowers x) : g₁ * g₂ = g₂ * g₁ := by
  obtain ⟨i, rfl | rfl⟩ := h.M_cases h₁ <;> obtain ⟨j, rfl | rfl⟩ := h.M_cases h₂
  · exact (Commute.zpow_zpow_self ρ i j).eq
  · rw [← mul_assoc, h.x_comm_zpow, mul_assoc, mul_assoc, (Commute.zpow_zpow_self ρ i j).eq]
  · rw [mul_assoc, (Commute.zpow_zpow_self ρ i j).eq, ← mul_assoc, ← h.x_comm_zpow, mul_assoc]
  · calc x * ρ ^ i * (x * ρ ^ j) = x * (ρ ^ i * x) * ρ ^ j := by group
      _ = x * (x * ρ ^ i) * ρ ^ j := by rw [h.x_comm_zpow]
      _ = x * (x * ρ ^ j) * ρ ^ i := by group
      _ = x * (ρ ^ j * x) * ρ ^ i := by rw [h.x_comm_zpow]
      _ = x * ρ ^ j * (x * ρ ^ i) := by group

theorem M_index_two [Finite G] (h : Config S t x ρ k) :
    (∀ g ∈ S, ∀ m ∈ zpowers ρ ⊔ zpowers x, g * m * g⁻¹ ∈ zpowers ρ ⊔ zpowers x) ∧
      (∀ a ∈ S, ∀ b ∈ S, a ∉ zpowers ρ ⊔ zpowers x → b ∉ zpowers ρ ⊔ zpowers x →
        a⁻¹ * b ∈ zpowers ρ ⊔ zpowers x) ∧ ⁅S, S⁆ ≤ zpowers ρ ⊔ zpowers x :=
  index_two_facts h.M_le h.card_S_eq

theorem t_mem_M (h : Config S t x ρ k) {m : G} (hm : m ∈ zpowers ρ ⊔ zpowers x) :
    t * m * t⁻¹ ∈ zpowers ρ ⊔ zpowers x := by
  obtain ⟨i, rfl | rfl⟩ := h.M_cases hm
  · rw [h.t_zpow]
    exact mem_sup_left (zpow_mem (mem_zpowers ρ) _)
  · have : t * (x * ρ ^ i) * t⁻¹ = (t * x * t⁻¹) * (t * ρ ^ i * t⁻¹) := by group
    rw [this, h.t_x, h.t_zpow]
    exact mul_mem (mem_sup_right (mem_zpowers x)) (mem_sup_left (zpow_mem (mem_zpowers ρ) _))

theorem mem_zpowers_rho_of_inv (h : Config S t x ρ k) {m : G}
    (hm : m ∈ zpowers ρ ⊔ zpowers x) (hinv : t * m * t⁻¹ = m⁻¹) : m ∈ zpowers ρ := by
  obtain ⟨i, rfl | rfl⟩ := h.M_cases hm
  · exact zpow_mem (mem_zpowers ρ) i
  · exfalso
    have h1 : t * (x * ρ ^ i) * t⁻¹ = x * ρ ^ (-i) := by
      have : t * (x * ρ ^ i) * t⁻¹ = (t * x * t⁻¹) * (t * ρ ^ i * t⁻¹) := by group
      rw [this, h.t_x, h.t_zpow]
    rw [h1, mul_inv_rev, ← h.x_comm_zpow, zpow_neg] at hinv
    have hx : x = x⁻¹ := mul_left_cancel hinv
    apply h.x_sq_ne_one
    rw [pow_two]
    nth_rewrite 2 [hx]
    exact mul_inv_cancel x

theorem mem_zpowers_x_of_fix (h : Config S t x ρ k) {g : G} (hg : g ∈ S)
    (hfix : t * g * t⁻¹ = g) : g ∈ zpowers x :=
  h.cent g hg (by
    calc g * t = t * g * t⁻¹ * t := by rw [hfix]
      _ = t * g := by group)

theorem t_conj_mem_S (h : Config S t x ρ k) {g : G} (hg : g ∈ S) : t * g * t⁻¹ ∈ S :=
  (mem_normalizer_iff.1 h.t_norm g).1 hg

theorem t_coset [Finite G] (h : Config S t x ρ k) {s : G} (hs : s ∈ S)
    (hsM : s ∉ zpowers ρ ⊔ zpowers x) : s⁻¹ * (t * s * t⁻¹) ∈ zpowers ρ ⊔ zpowers x := by
  refine h.M_index_two.2.1 s hs _ (h.t_conj_mem_S hs) hsM fun htM => hsM ?_
  have := h.t_mem_M htM
  rwa [h.t_inv, show t * (t * s * t) * t = (t * t) * s * (t * t) by group,
    ← pow_two, h.t_sq, one_mul, mul_one] at this

theorem conj_rho_mem [Finite G] (h : Config S t x ρ k) {s : G} (hs : s ∈ S) :
    s * ρ * s⁻¹ ∈ zpowers ρ := by
  by_cases hsM : s ∈ zpowers ρ ⊔ zpowers x
  · rw [h.M_comm hsM (mem_sup_left (mem_zpowers ρ)), mul_inv_cancel_right]
    exact mem_zpowers ρ
  · set m₀ := s⁻¹ * (t * s * t⁻¹) with hm₀
    have hm₀M : m₀ ∈ zpowers ρ ⊔ zpowers x := h.t_coset hs hsM
    have hts : t * s * t⁻¹ = s * m₀ := by rw [hm₀]; group
    have hwM : s * ρ * s⁻¹ ∈ zpowers ρ ⊔ zpowers x :=
      h.M_index_two.1 s hs ρ (mem_sup_left (mem_zpowers ρ))
    refine h.mem_zpowers_rho_of_inv hwM ?_
    have hcomm : m₀ * ρ⁻¹ = ρ⁻¹ * m₀ :=
      h.M_comm hm₀M (inv_mem (mem_sup_left (mem_zpowers ρ)))
    calc t * (s * ρ * s⁻¹) * t⁻¹ = (t * s * t⁻¹) * (t * ρ * t⁻¹) * (t * s * t⁻¹)⁻¹ := by group
      _ = s * (m₀ * ρ⁻¹) * m₀⁻¹ * s⁻¹ := by rw [hts, h.t_rho]; group
      _ = (s * ρ * s⁻¹)⁻¹ := by rw [hcomm]; group

theorem conj_x [Finite G] (h : Config S t x ρ k) {s : G} (hs : s ∈ S) :
    s * x * s⁻¹ = x ∨ s * x * s⁻¹ = x⁻¹ := by
  have hmem : s * x * s⁻¹ ∈ zpowers x := by
    by_cases hsM : s ∈ zpowers ρ ⊔ zpowers x
    · rw [h.M_comm hsM (mem_sup_right (mem_zpowers x)), mul_inv_cancel_right]
      exact mem_zpowers x
    · set m₀ := s⁻¹ * (t * s * t⁻¹) with hm₀
      have hm₀M : m₀ ∈ zpowers ρ ⊔ zpowers x := h.t_coset hs hsM
      have hts : t * s * t⁻¹ = s * m₀ := by rw [hm₀]; group
      refine h.mem_zpowers_x_of_fix (mul_mem (mul_mem hs h.x_mem) (inv_mem hs)) ?_
      have hcomm : m₀ * x = x * m₀ := h.M_comm hm₀M (mem_sup_right (mem_zpowers x))
      calc t * (s * x * s⁻¹) * t⁻¹ = (t * s * t⁻¹) * (t * x * t⁻¹) * (t * s * t⁻¹)⁻¹ := by
            group
        _ = s * (m₀ * x) * m₀⁻¹ * s⁻¹ := by rw [hts, h.t_x]; group
        _ = s * x * s⁻¹ := by rw [hcomm]; group
  have hsq : (s * x * s⁻¹) ^ 2 ≠ 1 := by
    rw [conj_pow]
    intro h1
    apply h.x_sq_ne_one
    calc x ^ 2 = s⁻¹ * (s * x ^ 2 * s⁻¹) * s := by group
      _ = 1 := by rw [h1]; group
  exact Lemma37.mem_zpowers_sq_ne_one h.x_order hmem hsq

theorem rho_zpow_eq_one_iff (h : Config S t x ρ k) (i : ℤ) : ρ ^ i = 1 ↔ (2 ^ k : ℤ) ∣ i := by
  rw [orderOf_dvd_iff_zpow_eq_one.symm, h.rho_order]
  push_cast
  rfl

@[expose] def y (_ : Config S t x ρ k) : G := ρ ^ 2 ^ (k - 2)

@[expose] def e (h : Config S t x ρ k) : G := h.y * x

theorem y_mem (h : Config S t x ρ k) : h.y ∈ zpowers ρ := pow_mem (mem_zpowers ρ) _

theorem y_sq (h : Config S t x ρ k) : h.y ^ 2 = x ^ 2 := by
  rw [Config.y, ← pow_mul, ← pow_succ, show k - 2 + 1 = k - 1 by have := h.hk; omega, h.rho_pow]

theorem y_comm_x (h : Config S t x ρ k) : h.y * x = x * h.y := (Commute.pow_left h.rho_x _).eq

theorem x_sq_comm_zpow (h : Config S t x ρ k) (i : ℤ) : ρ ^ i * x ^ 2 = x ^ 2 * ρ ^ i :=
  (Commute.pow_right (Commute.zpow_left h.rho_x i) 2).eq

theorem e_sq (h : Config S t x ρ k) : h.e ^ 2 = 1 := by
  rw [Config.e, Commute.mul_pow h.y_comm_x, h.y_sq, ← pow_add]
  exact h.x_pow_four

theorem e_mem_M (h : Config S t x ρ k) : h.e ∈ zpowers ρ ⊔ zpowers x :=
  mul_mem (mem_sup_left h.y_mem) (mem_sup_right (mem_zpowers x))

theorem e_mem (h : Config S t x ρ k) : h.e ∈ S := h.M_le h.e_mem_M

theorem e_not_mem (h : Config S t x ρ k) : h.e ∉ zpowers ρ := by
  intro he
  apply h.x_not_mem
  have : x = h.y⁻¹ * h.e := by rw [Config.e]; group
  rw [this]
  exact mul_mem (inv_mem h.y_mem) he

theorem e_comm_zpow (h : Config S t x ρ k) (i : ℤ) : h.e * ρ ^ i = ρ ^ i * h.e := by
  calc h.e * ρ ^ i = h.y * (x * ρ ^ i) := by rw [Config.e, mul_assoc]
    _ = h.y * ρ ^ i * x := by rw [← h.x_comm_zpow i, mul_assoc]
    _ = ρ ^ i * h.y * x := by
        rw [Config.y, (((Commute.refl ρ).pow_left (2 ^ (k - 2))).zpow_right i).eq]
    _ = ρ ^ i * h.e := by rw [Config.e, mul_assoc]

theorem y_comm_x_sq (h : Config S t x ρ k) : h.y * x ^ 2 = x ^ 2 * h.y :=
  (Commute.pow_right h.y_comm_x 2).eq

theorem y_inv (h : Config S t x ρ k) : h.y⁻¹ = h.y * x ^ 2 := by
  rw [inv_eq_iff_mul_eq_one, ← mul_assoc, ← pow_two, h.y_sq, ← pow_add]
  exact h.x_pow_four

theorem t_e (h : Config S t x ρ k) : t * h.e * t⁻¹ = x ^ 2 * h.e := by
  have hty : t * h.y * t⁻¹ = h.y⁻¹ := by
    rw [Config.y, ← zpow_natCast, h.t_zpow, zpow_neg]
  calc t * h.e * t⁻¹ = (t * h.y * t⁻¹) * (t * x * t⁻¹) := by rw [Config.e]; group
    _ = h.y * x ^ 2 * x := by rw [hty, h.t_x, h.y_inv]
    _ = x ^ 2 * h.e := by rw [h.y_comm_x_sq, mul_assoc, Config.e]

theorem M_cases_e (h : Config S t x ρ k) {g : G} (hg : g ∈ zpowers ρ ⊔ zpowers x) :
    ∃ i : ℤ, g = ρ ^ i ∨ g = ρ ^ i * h.e := by
  obtain ⟨i, rfl | rfl⟩ := h.M_cases hg
  · exact ⟨i, Or.inl rfl⟩
  · refine ⟨i - ((2 ^ (k - 2) : ℕ) : ℤ), Or.inr ?_⟩
    rw [Config.e, Config.y, ← mul_assoc, ← zpow_natCast, ← zpow_add, sub_add_cancel]
    exact (h.x_comm_zpow i).symm

theorem rho_zpow_sq (h : Config S t x ρ k) {i : ℤ} (hi : (ρ ^ i) ^ 2 = 1) :
    ρ ^ i = 1 ∨ ρ ^ i = x ^ 2 := by
  have h2 : (2 : ℤ) ^ k = 2 ^ (k - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel (by have := h.hk; omega)]
  rw [← zpow_natCast, ← zpow_mul, h.rho_zpow_eq_one_iff, h2] at hi
  obtain ⟨c, hc⟩ := hi
  have hi' : i = 2 ^ (k - 1) * c := by
    push_cast at hc
    linarith
  have hx2 : ρ ^ ((2 : ℤ) ^ (k - 1)) = x ^ 2 := by
    rw [← h.rho_pow, ← zpow_natCast]
    push_cast
    rfl
  have hx4 : (x ^ 2) ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← pow_two, ← pow_mul]
    exact h.x_pow_four
  rw [hi', zpow_mul, hx2]
  obtain ⟨d, rfl | rfl⟩ := Int.even_or_odd' c
  · left
    rw [zpow_mul, hx4, one_zpow]
  · right
    rw [zpow_add, zpow_one, zpow_mul, hx4, one_zpow, one_mul]

theorem M_involution (h : Config S t x ρ k) {g : G} (hg : g ∈ zpowers ρ ⊔ zpowers x)
    (hg2 : g ^ 2 = 1) : g = 1 ∨ g = x ^ 2 ∨ g = h.e ∨ g = x ^ 2 * h.e := by
  obtain ⟨i, rfl | rfl⟩ := h.M_cases_e hg
  · rcases h.rho_zpow_sq hg2 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · have hsq : (ρ ^ i) ^ 2 = 1 := by
      rwa [Commute.mul_pow (h.e_comm_zpow i).symm, h.e_sq, mul_one] at hg2
    rcases h.rho_zpow_sq hsq with h1 | h1
    · rw [h1, one_mul]
      exact Or.inr (Or.inr (Or.inl rfl))
    · rw [h1]
      exact Or.inr (Or.inr (Or.inr rfl))

theorem rho_zpow_four (h : Config S t x ρ k) {i : ℤ} (hi : (ρ ^ i) ^ 4 = 1) :
    ∃ j : ℤ, ρ ^ i = h.y ^ j := by
  have h4 : (2 : ℤ) ^ k = 2 ^ (k - 2) * 4 := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel h.hk]
  rw [← zpow_natCast, ← zpow_mul, h.rho_zpow_eq_one_iff, h4] at hi
  obtain ⟨c, hc⟩ := hi
  refine ⟨c, ?_⟩
  have hi' : i = 2 ^ (k - 2) * c := by
    push_cast at hc
    linarith
  rw [hi', Config.y, zpow_mul, ← zpow_natCast]
  push_cast
  rfl

theorem M_four (h : Config S t x ρ k) {g : G} (hg : g ∈ zpowers ρ ⊔ zpowers x)
    (hg4 : g ^ 4 = 1) : ∃ j : ℤ, g = h.y ^ j ∨ g = h.y ^ j * h.e := by
  have key : ∀ i : ℤ, (ρ ^ i) ^ 4 = 1 → ∃ j : ℤ, ρ ^ i = h.y ^ j := fun i hi =>
    h.rho_zpow_four hi
  obtain ⟨i, rfl | rfl⟩ := h.M_cases_e hg
  · obtain ⟨j, hj⟩ := key i hg4
    exact ⟨j, Or.inl hj⟩
  · have h4 : (ρ ^ i) ^ 4 = 1 := by
      rwa [Commute.mul_pow (h.e_comm_zpow i).symm, show h.e ^ 4 = (h.e ^ 2) ^ 2 by
        rw [← pow_mul], h.e_sq, one_pow, mul_one] at hg4
    obtain ⟨j, hj⟩ := key i h4
    exact ⟨j, Or.inr (by rw [hj])⟩

theorem x_inv_comm_zpow (h : Config S t x ρ k) (i : ℤ) : x⁻¹ * ρ ^ i = ρ ^ i * x⁻¹ :=
  (Commute.zpow_left h.rho_x i).inv_right.eq.symm

theorem commutator_le_of [Finite G] (h : Config S t x ρ k) {N : Subgroup G}
    (hNS : ∀ g ∈ S, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hcomm : ∀ g ∈ S, ∀ m ∈ zpowers ρ ⊔ zpowers x, g * m * g⁻¹ * m⁻¹ ∈ N) : ⁅S, S⁆ ≤ N := by
  rw [commutator_le]
  intro g hg g' hg'
  rw [commutatorElement_def]
  by_cases hg'M : g' ∈ zpowers ρ ⊔ zpowers x
  · exact hcomm g hg g' hg'M
  · by_cases hgM : g ∈ zpowers ρ ⊔ zpowers x
    · have := inv_mem (hcomm g' hg' g hgM)
      convert this using 1
      group
    · have hm := h.M_index_two.2.1 g hg g' hg' hgM hg'M
      have := hNS g hg _ (hcomm g hg _ hm)
      convert this using 1
      group

theorem commutator_le_zpowers_rho [Finite G] (h : Config S t x ρ k) : ⁅S, S⁆ ≤ zpowers ρ := by
  have hconj : ∀ g ∈ S, ∀ i : ℤ, g * ρ ^ i * g⁻¹ ∈ zpowers ρ := fun g hg i => by
    rw [← _root_.conj_zpow]
    exact zpow_mem (h.conj_rho_mem hg) i
  refine h.commutator_le_of (fun g hg n hn => ?_) (fun g hg m hm => ?_)
  · obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hn
    exact hconj g hg i
  · obtain ⟨i, rfl | rfl⟩ := h.M_cases hm
    · exact mul_mem (hconj g hg i) (inv_mem (zpow_mem (mem_zpowers ρ) i))
    · obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (hconj g hg i)
      have e1 : g * (x * ρ ^ i) * g⁻¹ * (x * ρ ^ i)⁻¹ =
          (g * x * g⁻¹) * (g * ρ ^ i * g⁻¹) * ρ ^ (-i) * x⁻¹ := by group
      rw [e1, ← hj]
      rcases h.conj_x hg with hx | hx <;> rw [hx]
      · have : x * ρ ^ j * ρ ^ (-i) * x⁻¹ = ρ ^ (j + -i) := by
          rw [mul_assoc x, ← zpow_add, ← h.x_comm_zpow, mul_inv_cancel_right]
        rw [this]
        exact zpow_mem (mem_zpowers ρ) _
      · have : x⁻¹ * ρ ^ j * ρ ^ (-i) * x⁻¹ = ρ ^ (j + -i) * (x ^ 2)⁻¹ := by
          rw [mul_assoc x⁻¹, ← zpow_add, h.x_inv_comm_zpow, mul_assoc, pow_two, mul_inv_rev]
        rw [this]
        exact mul_mem (zpow_mem (mem_zpowers ρ) _) (inv_mem h.x_sq_mem)

theorem two_pow_dvd_of_sq {k : ℕ} {c : ℤ} (hk : 2 ≤ k) (h1 : (2 : ℤ) ^ k ∣ (c - 1) * 2 ^ (k - 2))
    (h2 : (2 : ℤ) ^ k ∣ c ^ 2 - 1) : (2 : ℤ) ^ (k - 1) ∣ c - 1 := by
  obtain ⟨q, hq⟩ := h1
  have hc : c - 1 = 4 * q := by
    have h4 : (2 : ℤ) ^ k = 2 ^ (k - 2) * 4 := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel hk]
    rw [h4] at hq
    have hpos : (2 : ℤ) ^ (k - 2) ≠ 0 := by positivity
    exact mul_right_cancel₀ hpos (by rw [hq]; ring)
  rcases (show k ≤ 3 ∨ 4 ≤ k by omega) with hk3 | hk4
  · have h4 : (2 : ℤ) ^ (k - 1) ∣ 4 := by
      have : (2 : ℤ) ^ (k - 1) ∣ 2 ^ 2 := pow_dvd_pow 2 (by omega)
      simpa using this
    exact h4.trans ⟨q, hc⟩
  · obtain ⟨p, hp⟩ := h2
    have hexp : c ^ 2 - 1 = 8 * (q * (2 * q + 1)) := by
      have : c = 4 * q + 1 := by linarith
      rw [this]
      ring
    have h8 : (2 : ℤ) ^ k = 8 * 2 ^ (k - 3) := by
      rw [show (8 : ℤ) = 2 ^ 3 by norm_num, ← pow_add]
      congr 1
      omega
    have h' : (2 : ℤ) ^ (k - 3) ∣ q * (2 * q + 1) := by
      refine ⟨p, ?_⟩
      have : (8 : ℤ) * (q * (2 * q + 1)) = 8 * (2 ^ (k - 3) * p) := by
        rw [← hexp, hp, h8]
        ring
      linarith
    have hcop : IsCoprime ((2 : ℤ) ^ (k - 3)) (2 * q + 1) :=
      IsCoprime.pow_left ⟨-q, 1, by ring⟩
    obtain ⟨r, hr⟩ := hcop.dvd_of_dvd_mul_right h'
    refine ⟨r, ?_⟩
    have hk1 : (2 : ℤ) ^ (k - 1) = 4 * 2 ^ (k - 3) := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    rw [hc, hr, hk1]
    ring

theorem sq_mem_M [Finite G] (h : Config S t x ρ k) {g : G} (hg : g ∈ S) :
    g ^ 2 ∈ zpowers ρ ⊔ zpowers x := by
  by_cases hgM : g ∈ zpowers ρ ⊔ zpowers x
  · exact pow_mem hgM 2
  · have := h.M_index_two.2.1 g⁻¹ (inv_mem hg) g hg (fun h' => hgM (by simpa using inv_mem h'))
      hgM
    rwa [inv_inv, ← pow_two] at this

theorem rho_pow_z (h : Config S t x ρ k) : ρ ^ ((2 : ℤ) ^ (k - 1)) = x ^ 2 := by
  rw [← h.rho_pow, ← zpow_natCast]
  push_cast
  rfl

theorem conj_rho_of_central [Finite G] (h : Config S t x ρ k)
    (hy : ∀ g ∈ S, g * h.y = h.y * g) {g : G} (hg : g ∈ S) :
    g * ρ * g⁻¹ * ρ⁻¹ ∈ zpowers (x ^ 2) := by
  obtain ⟨c, hc⟩ := mem_zpowers_iff.1 (h.conj_rho_mem hg)
  have hpow : ∀ i : ℤ, g * ρ ^ i * g⁻¹ = ρ ^ (c * i) := fun i => by
    rw [← _root_.conj_zpow, ← hc, ← zpow_mul]
  have h1 : (2 : ℤ) ^ k ∣ (c - 1) * 2 ^ (k - 2) := by
    rw [← h.rho_zpow_eq_one_iff]
    have hy' : g * h.y * g⁻¹ = h.y := by rw [hy g hg, mul_inv_cancel_right]
    rw [Config.y, ← zpow_natCast, hpow] at hy'
    rw [show (c - 1) * (2 : ℤ) ^ (k - 2) = c * ((2 ^ (k - 2) : ℕ) : ℤ) - ((2 ^ (k - 2) : ℕ) : ℤ)
      by push_cast; ring, zpow_sub, hy', mul_inv_cancel]
  have h2 : (2 : ℤ) ^ k ∣ c ^ 2 - 1 := by
    rw [← h.rho_zpow_eq_one_iff]
    have hcomm : g ^ 2 * ρ = ρ * g ^ 2 := h.M_comm (h.sq_mem_M hg) (mem_sup_left (mem_zpowers ρ))
    have hc2 : g ^ 2 * ρ * (g ^ 2)⁻¹ = ρ ^ (c ^ 2) := by
      calc g ^ 2 * ρ * (g ^ 2)⁻¹ = g * (g * ρ * g⁻¹) * g⁻¹ := by rw [pow_two]; group
        _ = g * ρ ^ c * g⁻¹ := by rw [← hc]
        _ = ρ ^ (c ^ 2) := by rw [hpow, ← pow_two]
    rw [hcomm, mul_inv_cancel_right] at hc2
    rw [zpow_sub, ← hc2, zpow_one, mul_inv_cancel]
  obtain ⟨q, hq⟩ := two_pow_dvd_of_sq h.hk h1 h2
  refine mem_zpowers_iff.2 ⟨q, ?_⟩
  rw [← hc, ← h.rho_pow_z, ← zpow_mul, ← hq, zpow_sub, zpow_one]

theorem commutator_le_zpowers_z [Finite G] (h : Config S t x ρ k)
    (hy : ∀ g ∈ S, g * h.y = h.y * g) : ⁅S, S⁆ ≤ zpowers (x ^ 2) := by
  have hx2conj : ∀ g ∈ S, g * x ^ 2 * g⁻¹ = x ^ 2 := fun g hg => by
    rw [← conj_pow]
    rcases h.conj_x hg with hx | hx <;> rw [hx]
    rw [inv_pow, inv_eq_iff_mul_eq_one, ← pow_add]
    exact h.x_pow_four
  have hw : ∀ g ∈ S, ∀ i : ℤ, g * ρ ^ i * g⁻¹ * ρ ^ (-i) ∈ zpowers (x ^ 2) := by
    intro g hg i
    have hwmem := h.conj_rho_of_central hy hg
    set w := g * ρ * g⁻¹ * ρ⁻¹ with hwdef
    obtain ⟨q, hq⟩ := mem_zpowers_iff.1 hwmem
    have hwρ : Commute w ρ := by
      rw [← hq]
      exact (Commute.pow_left h.rho_x.symm 2).zpow_left q
    have hgρ : g * ρ * g⁻¹ = w * ρ := by rw [hwdef]; group
    have : g * ρ ^ i * g⁻¹ = w ^ i * ρ ^ i := by
      rw [← _root_.conj_zpow, hgρ, hwρ.mul_zpow]
    rw [this, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
    exact zpow_mem hwmem i
  refine h.commutator_le_of (fun g hg n hn => ?_) (fun g hg m hm => ?_)
  · obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hn
    rw [← _root_.conj_zpow, hx2conj g hg]
    exact zpow_mem (mem_zpowers _) j
  · obtain ⟨i, rfl | rfl⟩ := h.M_cases hm
    · rw [← zpow_neg]
      exact hw g hg i
    · have e1 : g * (x * ρ ^ i) * g⁻¹ * (x * ρ ^ i)⁻¹ =
          (g * x * g⁻¹) * (g * ρ ^ i * g⁻¹ * ρ ^ (-i)) * x⁻¹ := by group
      rw [e1]
      obtain ⟨q, hq⟩ := mem_zpowers_iff.1 (hw g hg i)
      rw [← hq]
      have hcx : Commute x ((x ^ 2) ^ q) := (Commute.self_pow x 2).zpow_right q
      rcases h.conj_x hg with hx | hx <;> rw [hx]
      · rw [hcx.eq, mul_inv_cancel_right]
        exact zpow_mem (mem_zpowers _) q
      · rw [hcx.inv_left.eq, mul_assoc, ← mul_inv_rev, ← pow_two]
        exact mul_mem (zpow_mem (mem_zpowers _) q) (inv_mem (mem_zpowers _))

theorem involution_outside [Finite G] (h : Config S t x ρ k) {u : G} (huS : u ∈ S)
    (huM : u ∉ zpowers ρ ⊔ zpowers x) (hu2 : u ^ 2 = 1) :
    u * ρ * u⁻¹ = ρ⁻¹ ∧ ∃ a : ℤ, Odd a ∧ t * u * t⁻¹ = u * ρ ^ a := by
  have htt : t * t = 1 := by rw [← pow_two, h.t_sq]
  have huu : u * u = 1 := by rw [← pow_two, hu2]
  set m₀ := u⁻¹ * (t * u * t⁻¹) with hm₀
  have hm₀M : m₀ ∈ zpowers ρ ⊔ zpowers x := h.t_coset huS huM
  have htu : t * u * t⁻¹ = u * m₀ := by rw [hm₀]; group
  have hτm₀ : t * m₀ * t⁻¹ = m₀⁻¹ := by
    have h1 : u * (m₀ * (t * m₀ * t⁻¹)) = u * 1 := by
      calc u * (m₀ * (t * m₀ * t⁻¹)) = (u * m₀) * (t * m₀ * t⁻¹) := by group
        _ = (t * u * t⁻¹) * (t * m₀ * t⁻¹) := by rw [htu]
        _ = t * (u * m₀) * t⁻¹ := by group
        _ = t * (t * u * t⁻¹) * t⁻¹ := by rw [htu]
        _ = (t * t) * u * (t * t)⁻¹ := by group
        _ = u * 1 := by rw [htt]; group
    exact eq_inv_of_mul_eq_one_right (mul_left_cancel h1)
  obtain ⟨a, ha⟩ := mem_zpowers_iff.1 (h.mem_zpowers_rho_of_inv hm₀M hτm₀)
  rw [← ha] at htu
  have hodd : Odd a := by
    rcases Int.even_or_odd a with ⟨b, hb⟩ | hodd
    · exfalso
      have hfix : t * (u * ρ ^ b) * t⁻¹ = u * ρ ^ b := by
        calc t * (u * ρ ^ b) * t⁻¹ = (t * u * t⁻¹) * (t * ρ ^ b * t⁻¹) := by group
          _ = u * ρ ^ a * ρ ^ (-b) := by rw [htu, h.t_zpow]
          _ = u * ρ ^ b := by rw [hb, mul_assoc, ← zpow_add]; ring_nf
      have hmem := h.mem_zpowers_x_of_fix (mul_mem huS (zpow_mem h.rho_mem b)) hfix
      apply huM
      have : u = (u * ρ ^ b) * ρ ^ (-b) := by group
      rw [this]
      exact mul_mem (mem_sup_right hmem) (mem_sup_left (zpow_mem (mem_zpowers ρ) _))
    · exact hodd
  refine ⟨?_, a, hodd, htu⟩
  obtain ⟨c, hc⟩ := mem_zpowers_iff.1 (h.conj_rho_mem huS)
  have hinv : (u * ρ ^ a) ^ 2 = 1 := by
    rw [← htu, conj_pow, hu2]
    group
  have hsq : (u * ρ ^ a) ^ 2 = ρ ^ (a * (c + 1)) := by
    calc (u * ρ ^ a) ^ 2 = (u * ρ ^ a * u⁻¹) * (u * u) * ρ ^ a := by rw [pow_two]; group
      _ = ρ ^ (a * (c + 1)) := by
          rw [huu, mul_one, ← _root_.conj_zpow, ← hc, ← zpow_mul, ← zpow_add]
          ring_nf
  rw [hsq, h.rho_zpow_eq_one_iff] at hinv
  obtain ⟨b, hb⟩ := hodd
  have hcop : IsCoprime ((2 : ℤ) ^ k) a := IsCoprime.pow_left ⟨-b, 1, by rw [hb]; ring⟩
  have hdvd := hcop.dvd_of_dvd_mul_left hinv
  rw [← h.rho_zpow_eq_one_iff, zpow_add, zpow_one] at hdvd
  rw [← hc]
  exact eq_inv_of_mul_eq_one_left hdvd

theorem S_cases [Finite G] (h : Config S t x ρ k) {u : G} (huS : u ∈ S)
    (huM : u ∉ zpowers ρ ⊔ zpowers x) {g : G} (hg : g ∈ S) :
    ∃ i : ℤ, g = ρ ^ i ∨ g = ρ ^ i * h.e ∨ g = u * ρ ^ i ∨ g = u * ρ ^ i * h.e := by
  by_cases hgM : g ∈ zpowers ρ ⊔ zpowers x
  · obtain ⟨i, rfl | rfl⟩ := h.M_cases_e hgM
    · exact ⟨i, Or.inl rfl⟩
    · exact ⟨i, Or.inr (Or.inl rfl)⟩
  · have hm := h.M_index_two.2.1 u huS g hg huM hgM
    have hgeq : g = u * (u⁻¹ * g) := by group
    obtain ⟨i, hi | hi⟩ := h.M_cases_e hm
    · exact ⟨i, Or.inr (Or.inr (Or.inl (by rw [hgeq, hi])))⟩
    · exact ⟨i, Or.inr (Or.inr (Or.inr (by rw [hgeq, hi, mul_assoc])))⟩

theorem u_e_of_inv (h : Config S t x ρ k) {u : G} (hur : u * ρ * u⁻¹ = ρ⁻¹)
    (hux : u * x * u⁻¹ = x⁻¹) : u * h.e * u⁻¹ = h.e := by
  have huy : u * h.y * u⁻¹ = h.y⁻¹ := by
    rw [Config.y, ← zpow_natCast, ← _root_.conj_zpow, hur, inv_zpow]
  calc u * h.e * u⁻¹ = (u * h.y * u⁻¹) * (u * x * u⁻¹) := by rw [Config.e]; group
    _ = (x * h.y)⁻¹ := by rw [huy, hux, mul_inv_rev]
    _ = h.e := by
        rw [← h.y_comm_x, ← Config.e, inv_eq_iff_mul_eq_one, ← pow_two, h.e_sq]

theorem u_e_of_comm (h : Config S t x ρ k) {u : G} (hur : u * ρ * u⁻¹ = ρ⁻¹)
    (hux : u * x * u⁻¹ = x) : u * h.e * u⁻¹ = x ^ 2 * h.e := by
  have huy : u * h.y * u⁻¹ = h.y⁻¹ := by
    rw [Config.y, ← zpow_natCast, ← _root_.conj_zpow, hur, inv_zpow]
  calc u * h.e * u⁻¹ = (u * h.y * u⁻¹) * (u * x * u⁻¹) := by rw [Config.e]; group
    _ = h.y * x ^ 2 * x := by rw [huy, hux, h.y_inv]
    _ = x ^ 2 * h.e := by rw [h.y_comm_x_sq, mul_assoc, Config.e]

end Config

end CFSG.ComponentClassification.AschbacherKnownGroup.ShapeExclusion
