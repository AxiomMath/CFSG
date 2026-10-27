module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitFusionZStar
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSylowTools
public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitFusion

public section

namespace CFSG.ComponentClassification.Foote47

open CFSG Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.FooteLit

variable {H : Type} [Group H]

theorem conj_mul' (g a b : H) : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group

theorem conj_mul_self {x : H} (hx : x * x = 1) (g : H) :
    (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := by
  calc (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
    _ = 1 := by rw [hx]; group

theorem mul_self_of_isConj {x y : H} (hx : x * x = 1) (h : IsConj x y) : y * y = 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact conj_mul_self hx g

theorem isConj_conj (x g : H) : IsConj x (g * x * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩

theorem eq_one_of_isConj_one {y : H} (h : IsConj (1 : H) y) : y = 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  group

theorem isPGroup_zpowers_of_mul_self {x : H} (hx : x * x = 1) : IsPGroup 2 (zpowers x) := by
  have hx2 : x ^ 2 ^ 1 = 1 := by rw [pow_one, sq]; exact hx
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx2)
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

theorem orderOf_eq_two_of_mul_self {x : H} (hx : x * x = 1) (h1 : x ≠ 1) : orderOf x = 2 :=
  orderOf_eq_prime (p := 2) (by rw [sq]; exact hx) h1

theorem mul_mul_self_of_comm {x y : H} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x) :
    (x * y) * (x * y) = 1 := by
  calc (x * y) * (x * y) = x * (y * x) * y := by group
    _ = x * (x * y) * y := by rw [hxy]
    _ = (x * x) * (y * y) := by group
    _ = 1 := by rw [hx, hy, one_mul]

theorem eq_one_of_two_pow_mul {j a b c : ℕ} (ha : ¬ 2 ∣ a) (hb : ¬ 2 ∣ b) (hc2 : 2 ∣ c)
    (hc4 : ¬ 4 ∣ c) (h : 2 ^ j * a = b * c) : j = 1 := by
  rcases j with _ | _ | j
  · exfalso
    apply ha
    rw [pow_zero, one_mul] at h
    rw [h]
    exact hc2.mul_left _
  · rfl
  · exfalso
    apply hc4
    have h4 : 4 ∣ b * c := by
      rw [← h, pow_succ, pow_succ, mul_assoc, mul_assoc]
      exact ⟨2 ^ j * a, by ring⟩
    have hcop : Nat.Coprime 4 b := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_left _ (Nat.prime_two.coprime_iff_not_dvd.mpr hb)
    exact hcop.dvd_of_dvd_mul_left h4

structure Resid (t t' : H) (P : Subgroup H) (S : Sylow 2 H) : Prop where
  ht : orderOf t = 2
  htt' : t ≠ t'
  hSyl : IsSylowOf 2 P (centralizer ({t} : Set H))
  hP : ∀ x : H, (x ∈ P ∧ IsConj t x) ↔ x = t ∨ x = t'
  hPS : P ≤ (S : Subgroup H)
  hidx : P.relIndex (S : Subgroup H) = 2

namespace Resid

variable {t t' : H} {P : Subgroup H} {S : Sylow 2 H}

theorem t_sq (h : Resid t t' P S) : t * t = 1 := by
  rw [← sq, ← h.ht, pow_orderOf_eq_one]

theorem t_inv (h : Resid t t' P S) : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq

theorem t_ne_one (h : Resid t t' P S) : t ≠ 1 := by
  intro h1
  have := h.ht
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem t'_mem (h : Resid t t' P S) : t' ∈ P := ((h.hP t').mpr (Or.inr rfl)).1

theorem t_mem (h : Resid t t' P S) : t ∈ P := ((h.hP t).mpr (Or.inl rfl)).1

theorem isConj_t' (h : Resid t t' P S) : IsConj t t' := ((h.hP t').mpr (Or.inr rfl)).2

theorem hPC (h : Resid t t' P S) : P ≤ centralizer ({t} : Set H) := h.hSyl.le

theorem t'_sq (h : Resid t t' P S) : t' * t' = 1 := mul_self_of_isConj h.t_sq h.isConj_t'

theorem comm_t' (h : Resid t t' P S) : t * t' = t' * t :=
  (mem_centralizer_singleton_iff.mp (h.hPC h.t'_mem)).symm

theorem z_sq (h : Resid t t' P S) : (t * t') * (t * t') = 1 :=
  mul_mul_self_of_comm h.t_sq h.t'_sq h.comm_t'

theorem z_ne_one (h : Resid t t' P S) : t * t' ≠ 1 := by
  intro h1
  apply h.htt'
  rw [eq_inv_of_mul_eq_one_right h1, h.t_inv]

theorem z_mem (h : Resid t t' P S) : t * t' ∈ P := mul_mem h.t_mem h.t'_mem

theorem t'_eq (h : Resid t t' P S) : t' = t * (t * t') := by
  rw [← mul_assoc, h.t_sq, one_mul]

theorem conj_mem_P (h : Resid t t' P S) {s p : H} (hs : s ∈ (S : Subgroup H)) (hp : p ∈ P) :
    s * p * s⁻¹ ∈ P := by
  have hn : (P.subgroupOf (S : Subgroup H)).Normal := normal_of_index_eq_two h.hidx
  have := hn.conj_mem ⟨p, h.hPS hp⟩ hp ⟨s, hs⟩
  exact this

theorem mul_mem_P_of_not_mem (h : Resid t t' P S) {a b : H} (ha : a ∈ (S : Subgroup H))
    (hb : b ∈ (S : Subgroup H)) (haP : a ∉ P) (hbP : b ∉ P) : a * b ∈ P := by
  have := (mul_mem_iff_of_index_two (a := (⟨a, ha⟩ : (S : Subgroup H))) (b := ⟨b, hb⟩)
    h.hidx).mpr (iff_of_false haP hbP)
  exact this

theorem mul_self_mem_P (h : Resid t t' P S) {a : H} (ha : a ∈ (S : Subgroup H)) : a * a ∈ P :=
  mul_self_mem_of_index_two (H := P.subgroupOf (S : Subgroup H)) h.hidx ⟨a, ha⟩

theorem mem_P_of_comm [Finite H] (h : Resid t t' P S) {s : H} (hs : s ∈ (S : Subgroup H))
    (hst : s * t = t * s) : s ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : P ≤ (S : Subgroup H) ⊓ centralizer ({t} : Set H) := le_inf h.hPS h.hPC
  have heq := h.hSyl.eq_of_le hle inf_le_right (S.isPGroup'.to_le inf_le_left)
  rw [← heq]
  exact ⟨hs, mem_centralizer_singleton_iff.mpr hst⟩

theorem conj_t_cases (h : Resid t t' P S) {s : H} (hs : s ∈ (S : Subgroup H)) :
    s * t * s⁻¹ = t ∨ s * t * s⁻¹ = t' :=
  (h.hP _).mp ⟨h.conj_mem_P hs h.t_mem, isConj_conj t s⟩

theorem conj_t_of_not_mem [Finite H] (h : Resid t t' P S) {s : H} (hs : s ∈ (S : Subgroup H))
    (hsP : s ∉ P) : s * t * s⁻¹ = t' := by
  rcases h.conj_t_cases hs with h1 | h1
  · exfalso
    apply hsP
    apply h.mem_P_of_comm hs
    calc s * t = s * t * s⁻¹ * s := by group
      _ = t * s := by rw [h1]
  · exact h1

theorem conj_z (h : Resid t t' P S) {s : H} (hs : s ∈ (S : Subgroup H)) :
    s * (t * t') * s⁻¹ = t * t' := by
  rw [conj_mul']
  have h1 := h.conj_t_cases hs
  have h2 : s * t' * s⁻¹ = t ∨ s * t' * s⁻¹ = t' :=
    (h.hP _).mp ⟨h.conj_mem_P hs h.t'_mem, h.isConj_t'.trans (isConj_conj t' s)⟩
  have hne : s * t * s⁻¹ ≠ s * t' * s⁻¹ := fun he => h.htt' (by simpa using he)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] at hne ⊢
  · exact absurd rfl hne
  · exact h.comm_t'.symm
  · exact absurd rfl hne

theorem S_le_centralizer_z (h : Resid t t' P S) :
    (S : Subgroup H) ≤ centralizer ({t * t'} : Set H) := fun s hs => by
  apply mem_centralizer_singleton_iff.mpr
  calc s * (t * t') = s * (t * t') * s⁻¹ * s := by group
    _ = t * t' * s := by rw [h.conj_z hs]

theorem exists_conj_t' [Finite H] (h : Resid t t' P S) :
    ∃ n ∈ (S : Subgroup H), n * t * n⁻¹ = t' := by
  have hlt : P ≠ (S : Subgroup H) := by
    intro he
    have := h.hidx
    rw [he, relIndex_self] at this
    exact absurd this (by norm_num)
  obtain ⟨n, hnS, hnP⟩ : ∃ n ∈ (S : Subgroup H), n ∉ P := by
    by_contra hcon
    push Not at hcon
    exact hlt (le_antisymm h.hPS hcon)
  exact ⟨n, hnS, h.conj_t_of_not_mem hnS hnP⟩

theorem isSylowOf_S [Finite H] (h : Resid t t' P S) :
    IsSylowOf 2 (S : Subgroup H) (centralizer ({t * t'} : Set H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff]
  refine ⟨h.S_le_centralizer_z, S.isPGroup', fun hd => S.not_dvd_index ?_⟩
  exact hd.trans (relIndex_dvd_index_of_le h.S_le_centralizer_z)

theorem exists_sylow (h : Resid t t' P S) :
    ∃ Q : Sylow 2 ↥(centralizer ({t} : Set H)),
      (Q : Subgroup _).map (centralizer ({t} : Set H)).subtype = P :=
  h.hSyl

theorem comm_cases [Finite H] (h : Resid t t' P S) {x : H} (hxt : IsConj t x)
    (hcomm : x * t = t * x) :
    x = t ∨ ∃ c ∈ centralizer ({t} : Set H), x = c * t' * c⁻¹ := by
  obtain ⟨Q, hQ⟩ := h.exists_sylow
  exact conj_comm_cases h.ht Q (by rw [hQ]; exact h.hP) hxt hcomm

theorem P_le_centralizer_t' (h : Resid t t' P S) : P ≤ centralizer ({t'} : Set H) := by
  intro p hp
  have hpt : p * t = t * p := mem_centralizer_singleton_iff.mp (h.hPC hp)
  have hconj : p * t' * p⁻¹ ∈ P ∧ IsConj t (p * t' * p⁻¹) :=
    ⟨mul_mem (mul_mem hp h.t'_mem) (inv_mem hp), h.isConj_t'.trans (isConj_conj t' p)⟩
  rcases (h.hP _).mp hconj with h1 | h1
  · exfalso
    apply h.htt'
    calc t = p⁻¹ * (p * t) * p⁻¹⁻¹ * p⁻¹ := by group
      _ = p⁻¹ * (t * p) * p⁻¹⁻¹ * p⁻¹ := by rw [hpt]
      _ = p⁻¹ * (p * t' * p⁻¹) * p := by rw [← h1]; group
      _ = t' := by group
  · apply mem_centralizer_singleton_iff.mpr
    calc p * t' = p * t' * p⁻¹ * p := by group
      _ = t' * p := by rw [h1]

theorem eq_of_comm_t_t' [Finite H] (h : Resid t t' P S) {y : H} (hy : IsConj t y)
    (hyt : y * t = t * y) (hyt' : y * t' = t' * y) : y = t ∨ y = t' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := centralizer ({t} : Set H) ⊓ centralizer ({t'} : Set H) with hD
  have hPD : P ≤ D := le_inf h.hPC h.P_le_centralizer_t'
  have hSD : IsSylowOf 2 P D := h.hSyl.of_le hPD inf_le_left
  have hyD : zpowers y ≤ D := zpowers_le.mpr
    ⟨mem_centralizer_singleton_iff.mpr hyt, mem_centralizer_singleton_iff.mpr hyt'⟩
  obtain ⟨k, hkD, hk⟩ := exists_conj_le_of_isSylowOf hSD hyD
    (isPGroup_zpowers_of_mul_self (mul_self_of_isConj h.t_sq hy))
  have hky := hk y (mem_zpowers y)
  have hkt : k * t = t * k := mem_centralizer_singleton_iff.mp hkD.1
  have hkt' : k * t' = t' * k := mem_centralizer_singleton_iff.mp hkD.2
  have hconj : IsConj t (k⁻¹ * y * k) := hy.trans (isConj_iff.mpr ⟨k⁻¹, by group⟩)
  rcases (h.hP _).mp ⟨hky, hconj⟩ with h1 | h1
  · left
    calc y = k * (k⁻¹ * y * k) * k⁻¹ := by group
      _ = k * t * k⁻¹ := by rw [h1]
      _ = t := by rw [hkt]; group
  · right
    calc y = k * (k⁻¹ * y * k) * k⁻¹ := by group
      _ = k * t' * k⁻¹ := by rw [h1]
      _ = t' := by rw [hkt']; group

theorem eq_of_comm [Finite H] (h : Resid t t' P S) {y₁ y₂ : H} (hy₁ : IsConj t y₁)
    (hy₂ : IsConj t y₂) (h₁ : y₁ * t = t * y₁) (h₂ : y₂ * t = t * y₂)
    (h₁₂ : y₁ * y₂ = y₂ * y₁) (hne₁ : y₁ ≠ t) (hne₂ : y₂ ≠ t) : y₁ = y₂ := by
  rcases h.comm_cases hy₁ h₁ with h1 | ⟨c, hc, rfl⟩
  · exact absurd h1 hne₁
  have hct : c * t = t * c := mem_centralizer_singleton_iff.mp hc
  set y := c⁻¹ * y₂ * c with hydef
  have hy : IsConj t y := hy₂.trans (isConj_iff.mpr ⟨c⁻¹, by rw [hydef]; group⟩)
  have hct' : c⁻¹ * t * c = t := by
    calc c⁻¹ * t * c = c⁻¹ * (t * c) := by group
      _ = c⁻¹ * (c * t) := by rw [hct]
      _ = t := by group
  have hcit : c⁻¹ * t = t * c⁻¹ := mem_centralizer_singleton_iff.mp (inv_mem hc)
  have hyt : y * t = t * y := by
    calc y * t = c⁻¹ * y₂ * (c * t) := by rw [hydef]; group
      _ = c⁻¹ * (y₂ * t) * c := by rw [hct]; group
      _ = c⁻¹ * (t * y₂) * c := by rw [h₂]
      _ = (c⁻¹ * t) * y₂ * c := by group
      _ = t * y := by rw [hcit, hydef]; group
  have hyt' : y * t' = t' * y := by
    calc y * t' = c⁻¹ * (y₂ * (c * t' * c⁻¹)) * c := by rw [hydef]; group
      _ = c⁻¹ * ((c * t' * c⁻¹) * y₂) * c := by rw [h₁₂]
      _ = t' * y := by rw [hydef]; group
  rcases h.eq_of_comm_t_t' hy hyt hyt' with h1 | h1
  · exfalso
    apply hne₂
    calc y₂ = c * y * c⁻¹ := by rw [hydef]; group
      _ = c * t * c⁻¹ := by rw [h1]
      _ = t := by rw [hct]; group
  · calc c * t' * c⁻¹ = c * y * c⁻¹ := by rw [h1]
      _ = y₂ := by rw [hydef]; group

theorem conj_of_comm_z [Finite H] (h : Resid t t' P S) {x : H} (hx : IsConj t x)
    (hxz : x * (t * t') = (t * t') * x) :
    ∃ m ∈ centralizer ({t * t'} : Set H), x = m * t * m⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : x * x = 1 := mul_self_of_isConj h.t_sq hx
  obtain ⟨k, hkC, hk⟩ := exists_conj_le_of_isSylowOf h.isSylowOf_S
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxz)) (isPGroup_zpowers_of_mul_self hx2)
  set x₀ := k⁻¹ * x * k with hx₀
  have hx₀S : x₀ ∈ (S : Subgroup H) := hk x (mem_zpowers x)
  have hx₀c : IsConj t x₀ := hx.trans (isConj_iff.mpr ⟨k⁻¹, by rw [hx₀]; group⟩)
  have hx₀2 : x₀ * x₀ = 1 := mul_self_of_isConj h.t_sq hx₀c
  have hkx : x = k * x₀ * k⁻¹ := by rw [hx₀]; group
  suffices hsuff : ∃ m ∈ centralizer ({t * t'} : Set H), x₀ = m * t * m⁻¹ by
    obtain ⟨m, hm, hmx⟩ := hsuff
    refine ⟨k * m, mul_mem hkC hm, ?_⟩
    rw [hkx, hmx]
    group
  by_cases hx₀P : x₀ ∈ P
  · rcases (h.hP x₀).mp ⟨hx₀P, hx₀c⟩ with h1 | h1
    · exact ⟨1, one_mem _, by rw [h1]; group⟩
    · obtain ⟨n, hnS, hn⟩ := h.exists_conj_t'
      exact ⟨n, h.S_le_centralizer_z hnS, by rw [h1, hn]⟩
  ·
    have hconj := h.conj_t_of_not_mem hx₀S hx₀P
    have hx₀z : x₀ * (t * t') = (t * t') * x₀ :=
      mem_centralizer_singleton_iff.mp (h.S_le_centralizer_z hx₀S)
    have htx : t * x₀ * t⁻¹ = (t * t') * x₀ := by
      calc t * x₀ * t⁻¹ = t * (x₀ * t * x₀⁻¹) * x₀ := by rw [h.t_inv]; group
        _ = (t * t') * x₀ := by rw [hconj]
    obtain ⟨a, ha⟩ := isConj_iff.mp hx₀c
    obtain ⟨x₁, hx₁⟩ : ∃ x₁, x₁ = (t * t') * x₀ := ⟨_, rfl⟩
    have hx₁c : IsConj t x₁ := by
      rw [hx₁, ← htx]
      exact hx₀c.trans (isConj_conj x₀ t)
    have e2 : x₁ * x₀ = x₀ * x₁ := by
      calc x₁ * x₀ = (t * t') * x₀ * x₀ := by rw [hx₁]
        _ = x₀ * (t * t') * x₀ := by rw [← hx₀z]
        _ = x₀ * x₁ := by rw [hx₁]; group
    have hy : IsConj t (a⁻¹ * x₁ * a) := hx₁c.trans (isConj_iff.mpr ⟨a⁻¹, by group⟩)
    have e1 : t = a⁻¹ * x₀ * a := by rw [← ha]; group
    have hycomm : (a⁻¹ * x₁ * a) * t = t * (a⁻¹ * x₁ * a) := by
      calc (a⁻¹ * x₁ * a) * t = a⁻¹ * (x₁ * x₀) * a := by rw [e1]; group
        _ = a⁻¹ * (x₀ * x₁) * a := by rw [e2]
        _ = t * (a⁻¹ * x₁ * a) := by rw [e1]; group
    rcases h.comm_cases hy hycomm with h1 | ⟨c, hc, hc'⟩
    · exfalso
      have : x₁ = x₀ := by
        calc x₁ = a * (a⁻¹ * x₁ * a) * a⁻¹ := by group
          _ = a * t * a⁻¹ := by rw [h1]
          _ = x₀ := ha
      apply h.z_ne_one
      calc t * t' = x₁ * x₀⁻¹ := by rw [hx₁]; group
        _ = 1 := by rw [this, mul_inv_cancel]
    · have hct : c * t = t * c := mem_centralizer_singleton_iff.mp hc
      have e3 : (a * c) * t * (a * c)⁻¹ = x₀ := by
        calc (a * c) * t * (a * c)⁻¹ = a * (c * t) * c⁻¹ * a⁻¹ := by group
          _ = a * t * a⁻¹ := by rw [hct]; group
          _ = x₀ := ha
      have e4 : (a * c) * t' * (a * c)⁻¹ = x₁ := by
        calc (a * c) * t' * (a * c)⁻¹ = a * (c * t' * c⁻¹) * a⁻¹ := by group
          _ = a * (a⁻¹ * x₁ * a) * a⁻¹ := by rw [← hc']
          _ = x₁ := by group
      have e5 : (a * c) * (t * t') * (a * c)⁻¹ = t * t' := by
        rw [conj_mul', e3, e4, hx₁]
        calc x₀ * (t * t' * x₀) = (x₀ * (t * t')) * x₀ := by group
          _ = (t * t') * x₀ * x₀ := by rw [hx₀z]
          _ = t * t' := by rw [mul_assoc, hx₀2, mul_one]
      refine ⟨a * c, ?_, ?_⟩
      · apply mem_centralizer_singleton_iff.mpr
        calc (a * c) * (t * t') = (a * c) * (t * t') * (a * c)⁻¹ * (a * c) := by group
          _ = t * t' * (a * c) := by rw [e5]
      · exact e3.symm

theorem isConj_t_mul [Finite H] (h : Resid t t' P S) {w : H} (hw : IsConj (t * t') w)
    (hwt : w * t = t * w) : IsConj t (t * w) := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hw
  have hxz : (g⁻¹ * t * g) * (t * t') = (t * t') * (g⁻¹ * t * g) := by
    calc (g⁻¹ * t * g) * (t * t') = g⁻¹ * (t * (g * (t * t') * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * (t * t') * g⁻¹) * t) * g := by rw [hwt]
      _ = (t * t') * (g⁻¹ * t * g) := by group
  obtain ⟨m, hm, hmx⟩ := h.conj_of_comm_z (isConj_iff.mpr ⟨g⁻¹, by group⟩) hxz
  have hmz : m * (t * t') * m⁻¹ = t * t' := by
    rw [mem_centralizer_singleton_iff.mp hm]
    group
  have e1 : (g * m) * t * (g * m)⁻¹ = t := by
    calc (g * m) * t * (g * m)⁻¹ = g * (m * t * m⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * t * g) * g⁻¹ := by rw [← hmx]
      _ = t := by group
  have e2 : (g * m) * (t * t') * (g * m)⁻¹ = g * (t * t') * g⁻¹ := by
    calc (g * m) * (t * t') * (g * m)⁻¹ = g * (m * (t * t') * m⁻¹) * g⁻¹ := by group
      _ = g * (t * t') * g⁻¹ := by rw [hmz]
  have e3 : (g * m) * t' * (g * m)⁻¹ = t * (g * (t * t') * g⁻¹) := by
    conv_lhs => rw [h.t'_eq]
    rw [conj_mul', e1, e2]
  rw [← e3]
  exact h.isConj_t'.trans (isConj_conj t' (g * m))

theorem ne_one_of_isConj_z (h : Resid t t' P S) {w : H} (hw : IsConj (t * t') w) : w ≠ 1 := by
  rintro rfl
  exact h.z_ne_one (eq_one_of_isConj_one hw.symm)

theorem eq_of_comm_conj_z [Finite H] (h : Resid t t' P S) {w₁ w₂ : H}
    (hw₁ : IsConj (t * t') w₁) (hw₂ : IsConj (t * t') w₂) (h₁ : w₁ * t = t * w₁)
    (h₂ : w₂ * t = t * w₂) (h₁₂ : w₁ * w₂ = w₂ * w₁) : w₁ = w₂ := by
  have hne : ∀ {w : H}, IsConj (t * t') w → t * w ≠ t := fun hw he =>
    h.ne_one_of_isConj_z hw (by simpa using he)
  have c₁ : (t * w₁) * t = t * (t * w₁) := by rw [mul_assoc, h₁]
  have c₂ : (t * w₂) * t = t * (t * w₂) := by rw [mul_assoc, h₂]
  have c₁₂ : (t * w₁) * (t * w₂) = (t * w₂) * (t * w₁) := by
    calc (t * w₁) * (t * w₂) = t * (w₁ * t) * w₂ := by group
      _ = t * t * (w₁ * w₂) := by rw [h₁]; group
      _ = t * t * (w₂ * w₁) := by rw [h₁₂]
      _ = t * (w₂ * t) * w₁ := by rw [h₂]; group
      _ = (t * w₂) * (t * w₁) := by group
  exact mul_left_cancel (h.eq_of_comm (h.isConj_t_mul hw₁ h₁) (h.isConj_t_mul hw₂ h₂) c₁ c₂
    c₁₂ (hne hw₁) (hne hw₂))

theorem eq_z_of_mem [Finite H] (h : Resid t t' P S) {w : H} (hw : IsConj (t * t') w)
    (hwP : w ∈ P) : w = t * t' := by
  have hwt : w * t = t * w := mem_centralizer_singleton_iff.mp (h.hPC hwP)
  rcases (h.hP (t * w)).mp ⟨mul_mem h.t_mem hwP, h.isConj_t_mul hw hwt⟩ with h1 | h1
  · exact absurd (by simpa using h1) (h.ne_one_of_isConj_z hw)
  · calc w = t⁻¹ * (t * w) := by group
      _ = t * t' := by rw [h1, h.t_inv]

theorem z_mem_S (h : Resid t t' P S) : t * t' ∈ (S : Subgroup H) := h.hPS h.z_mem

theorem t_mem_S (h : Resid t t' P S) : t ∈ (S : Subgroup H) := h.hPS h.t_mem

theorem comm_z (h : Resid t t' P S) {s : H} (hs : s ∈ (S : Subgroup H)) :
    s * (t * t') = (t * t') * s :=
  mem_centralizer_singleton_iff.mp (h.S_le_centralizer_z hs)

theorem not_comm [Finite H] (h : Resid t t' P S) {x w : H} (hxS : x ∈ (S : Subgroup H))
    (hx : IsConj t x) (hwS : w ∈ (S : Subgroup H)) (hw : IsConj (t * t') w)
    (hwz : w ≠ t * t') : x * w ≠ w * x := by
  intro hxw
  obtain ⟨m, hm, rfl⟩ := h.conj_of_comm_z hx (h.comm_z hxS)
  have hmz : m * (t * t') = (t * t') * m := mem_centralizer_singleton_iff.mp hm
  have hmz' : m⁻¹ * (t * t') = (t * t') * m⁻¹ := mem_centralizer_singleton_iff.mp (inv_mem hm)
  have hw' : IsConj (t * t') (m⁻¹ * w * m) := hw.trans (isConj_iff.mpr ⟨m⁻¹, by group⟩)
  have h₁ : (m⁻¹ * w * m) * t = t * (m⁻¹ * w * m) := by
    calc (m⁻¹ * w * m) * t = m⁻¹ * (w * (m * t * m⁻¹)) * m := by group
      _ = m⁻¹ * ((m * t * m⁻¹) * w) * m := by rw [hxw]
      _ = t * (m⁻¹ * w * m) := by group
  have h₂ : (t * t') * t = t * (t * t') := by rw [mul_assoc, ← h.comm_t']
  have h₁₂ : (m⁻¹ * w * m) * (t * t') = (t * t') * (m⁻¹ * w * m) := by
    calc (m⁻¹ * w * m) * (t * t') = m⁻¹ * w * (m * (t * t')) := by group
      _ = m⁻¹ * (w * (t * t')) * m := by rw [hmz]; group
      _ = m⁻¹ * ((t * t') * w) * m := by rw [h.comm_z hwS]
      _ = (m⁻¹ * (t * t')) * w * m := by group
      _ = (t * t') * (m⁻¹ * w * m) := by rw [hmz']; group
  have he := h.eq_of_comm_conj_z hw' (IsConj.refl _) h₁ h₂ h₁₂
  apply hwz
  calc w = m * (m⁻¹ * w * m) * m⁻¹ := by group
    _ = m * (t * t') * m⁻¹ := by rw [he]
    _ = t * t' := by rw [hmz]; group

theorem not_mem_P [Finite H] (h : Resid t t' P S) {w : H} (hw : IsConj (t * t') w)
    (hwz : w ≠ t * t') : w ∉ P := fun hwP => hwz (h.eq_z_of_mem hw hwP)

theorem conj_t_w [Finite H] (h : Resid t t' P S) {w : H} (hwS : w ∈ (S : Subgroup H))
    (hw : IsConj (t * t') w) (hwz : w ≠ t * t') : t * w * t⁻¹ = (t * t') * w := by
  have hconj := h.conj_t_of_not_mem hwS (h.not_mem_P hw hwz)
  calc t * w * t⁻¹ = t * w * t := by rw [h.t_inv]
    _ = t * (w * t * w⁻¹) * w := by group
    _ = (t * t') * w := by rw [hconj]

theorem isConj_z_mul [Finite H] (h : Resid t t' P S) {w : H} (hwS : w ∈ (S : Subgroup H))
    (hw : IsConj (t * t') w) (hwz : w ≠ t * t') : IsConj (t * t') ((t * t') * w) := by
  rw [← h.conj_t_w hwS hw hwz]
  exact hw.trans (isConj_conj w t)

theorem sq_t_mul [Finite H] (h : Resid t t' P S) {w : H} (hwS : w ∈ (S : Subgroup H))
    (hw : IsConj (t * t') w) (hwz : w ≠ t * t') : (t * w) ^ 2 = t * t' := by
  have e := h.conj_t_w hwS hw hwz
  rw [h.t_inv] at e
  calc (t * w) ^ 2 = (t * w * t) * w := by rw [sq]; group
    _ = (t * t') * (w * w) := by rw [e]; group
    _ = t * t' := by rw [mul_self_of_isConj h.z_sq hw, mul_one]

theorem exists_conj_sylow [Finite H] (h : Resid t t' P S) {w : H} (hw : IsConj (t * t') w) :
    ∃ g₁ : H, g₁ * (t * t') * g₁⁻¹ = w ∧
      ∀ a ∈ (S : Subgroup H), a * w = w * a → g₁⁻¹ * a * g₁ ∈ (S : Subgroup H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, rfl⟩ := isConj_iff.mp hw
  have hmem : ∀ x : H, x ∈ ((g • S : Sylow 2 H) : Subgroup H) ↔ g⁻¹ * x * g ∈ (S : Subgroup H) := by
    intro x
    rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
      MulAut.conj_apply, inv_inv]
  have hle : ((g • S : Sylow 2 H) : Subgroup H) ≤ centralizer ({g * (t * t') * g⁻¹} : Set H) := by
    intro x hx
    rw [hmem] at hx
    have e := h.comm_z hx
    apply mem_centralizer_singleton_iff.mpr
    calc x * (g * (t * t') * g⁻¹) = g * ((g⁻¹ * x * g) * (t * t')) * g⁻¹ := by group
      _ = g * ((t * t') * (g⁻¹ * x * g)) * g⁻¹ := by rw [e]
      _ = g * (t * t') * g⁻¹ * x := by group
  have hsyl : IsSylowOf 2 ((g • S : Sylow 2 H) : Subgroup H)
      (centralizer ({g * (t * t') * g⁻¹} : Set H)) := by
    rw [isSylowOf_iff]
    exact ⟨hle, (g • S).isPGroup', fun hd =>
      (g • S).not_dvd_index (hd.trans (relIndex_dvd_index_of_le hle))⟩
  obtain ⟨c, hcC, hc⟩ := exists_conj_le_of_isSylowOf hsyl
    (inf_le_right : (S : Subgroup H) ⊓ centralizer ({g * (t * t') * g⁻¹} : Set H) ≤ _)
    (S.isPGroup'.to_le inf_le_left)
  refine ⟨c * g, ?_, ?_⟩
  · have hc' := mem_centralizer_singleton_iff.mp hcC
    calc c * g * (t * t') * (c * g)⁻¹ = c * (g * (t * t') * g⁻¹) * c⁻¹ := by group
      _ = g * (t * t') * g⁻¹ := by rw [hc']; group
  · intro a haS haw
    have h1 := hc a ⟨haS, mem_centralizer_singleton_iff.mpr haw⟩
    rw [hmem] at h1
    have e : (c * g)⁻¹ * a * (c * g) = g⁻¹ * (c⁻¹ * a * c) * g := by group
    rw [e]
    exact h1

theorem eq_z_mul_of_comm [Finite H] (h : Resid t t' P S) {w₁ w₂ : H}
    (hw₁S : w₁ ∈ (S : Subgroup H)) (hw₁ : IsConj (t * t') w₁) (hw₁z : w₁ ≠ t * t')
    (hw₂S : w₂ ∈ (S : Subgroup H)) (hw₂ : IsConj (t * t') w₂) (hw₂z : w₂ ≠ t * t')
    (h₁₂ : w₁ * w₂ = w₂ * w₁) (hne : w₂ ≠ w₁) : w₂ = (t * t') * w₁ := by
  obtain ⟨g₁, hg₁, hS₁⟩ := h.exists_conj_sylow hw₁
  have hback : ∀ {v : H}, IsConj (t * t') v → g₁⁻¹ * v * g₁ ∈ P → v = w₁ := by
    intro v hv hvP
    have e := h.eq_z_of_mem (hv.trans (isConj_iff.mpr ⟨g₁⁻¹, by group⟩)) hvP
    calc v = g₁ * (g₁⁻¹ * v * g₁) * g₁⁻¹ := by group
      _ = w₁ := by rw [e, hg₁]
  have hzS := hS₁ (t * t') h.z_mem_S (h.comm_z hw₁S).symm
  have hw₂S' := hS₁ w₂ hw₂S h₁₂.symm
  have hzP : g₁⁻¹ * (t * t') * g₁ ∉ P := fun hP => hw₁z (hback (IsConj.refl _) hP).symm
  have hw₂P : g₁⁻¹ * w₂ * g₁ ∉ P := fun hP => hne (hback hw₂ hP)
  have hprod := h.mul_mem_P_of_not_mem hzS hw₂S' hzP hw₂P
  have e : g₁⁻¹ * (t * t') * g₁ * (g₁⁻¹ * w₂ * g₁) = g₁⁻¹ * ((t * t') * w₂) * g₁ := by group
  rw [e] at hprod
  have he := hback (h.isConj_z_mul hw₂S hw₂ hw₂z) hprod
  calc w₂ = (t * t') * ((t * t') * w₂) := by
        rw [← mul_assoc, h.z_sq, one_mul]
    _ = (t * t') * w₁ := by rw [he]

theorem comm_of_mem [Finite H] (h : Resid t t' P S) {w₁ w₂ : H}
    (hw₁S : w₁ ∈ (S : Subgroup H)) (hw₁ : IsConj (t * t') w₁) (hw₁z : w₁ ≠ t * t')
    (hw₂S : w₂ ∈ (S : Subgroup H)) (hw₂ : IsConj (t * t') w₂) (hw₂z : w₂ ≠ t * t') :
    w₁ * w₂ = w₂ * w₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnc
  have hw₁2 : w₁ * w₁ = 1 := mul_self_of_isConj h.z_sq hw₁
  have hw₁inv : w₁⁻¹ = w₁ := inv_eq_of_mul_eq_one_right hw₁2
  have hw₂inv : w₂⁻¹ = w₂ := inv_eq_of_mul_eq_one_right (mul_self_of_isConj h.z_sq hw₂)
  obtain ⟨u, hu⟩ : ∃ u, u = w₁ * w₂ := ⟨_, rfl⟩
  have huP : u ∈ P := by
    rw [hu]
    exact h.mul_mem_P_of_not_mem hw₁S hw₂S (h.not_mem_P hw₁ hw₁z) (h.not_mem_P hw₂ hw₂z)
  have huS : u ∈ (S : Subgroup H) := h.hPS huP
  have hinv : w₁ * u * w₁⁻¹ = u⁻¹ := by
    calc w₁ * u * w₁⁻¹ = (w₁ * w₁) * w₂ * w₁⁻¹ := by rw [hu]; group
      _ = w₂⁻¹ * w₁⁻¹ := by rw [hw₁2, one_mul, hw₂inv]
      _ = u⁻¹ := by rw [hu, mul_inv_rev]
  have hinvn : ∀ n : ℕ, w₁ * u ^ n * w₁⁻¹ = (u ^ n)⁻¹ := fun n => by
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hinv, inv_pow]
  have huu : u * u ≠ 1 := by
    intro h1
    apply hnc
    have e : u = u⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    calc w₁ * w₂ = u := hu.symm
      _ = u⁻¹ := e
      _ = w₂⁻¹ * w₁⁻¹ := by rw [hu, mul_inv_rev]
      _ = w₂ * w₁ := by rw [hw₁inv, hw₂inv]
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp S.isPGroup') ⟨u, huS⟩
  rw [Subgroup.orderOf_mk] at ha
  rcases a with _ | _ | b
  · have hu1 : u = 1 := orderOf_eq_one_iff.mp (by simpa using ha)
    exact huu (by rw [hu1, one_mul])
  · exact huu (by rw [← sq, ← pow_one 2, ← ha, pow_orderOf_eq_one])
  set v := u ^ (2 ^ b) with hv
  have hvP : v ∈ P := pow_mem huP _
  have hvS : v ∈ (S : Subgroup H) := h.hPS hvP
  have hvv : v * v = u ^ (2 ^ (b + 1)) := by rw [hv, ← pow_add, pow_succ, mul_two]
  have hc1 : v * v ≠ 1 := by
    rw [hvv]
    intro h1
    have hd := orderOf_dvd_of_pow_eq_one h1
    rw [ha] at hd
    have := Nat.le_of_dvd (by positivity) hd
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp this
    omega
  have hcc : (v * v) * (v * v) = 1 := by
    rw [hvv, ← pow_add, ← two_mul, ← pow_succ', ← ha, pow_orderOf_eq_one]
  have hcP : v * v ∈ P := mul_mem hvP hvP
  have hvw : w₁ * v * w₁⁻¹ = v⁻¹ := hinvn _
  have hvw' : v⁻¹ * w₁ = w₁ * v := by
    calc v⁻¹ * w₁ = w₁ * v * w₁⁻¹ * w₁ := by rw [hvw]
      _ = w₁ * v := by group
  have hconjc : IsConj w₁ (w₁ * (v * v)) := by
    refine isConj_iff.mpr ⟨v⁻¹, ?_⟩
    calc v⁻¹ * w₁ * v⁻¹⁻¹ = (v⁻¹ * w₁) * v := by group
      _ = w₁ * (v * v) := by rw [hvw']; group
  have hcw : w₁ * (v * v) = (v * v) * w₁ := by
    have e : w₁ * (v * v) * w₁⁻¹ = (v * v)⁻¹ := by
      rw [show v * v = u ^ (2 ^ (b + 1)) from hvv, hinvn]
    have e2 : (v * v)⁻¹ = v * v := inv_eq_of_mul_eq_one_right hcc
    calc w₁ * (v * v) = w₁ * (v * v) * w₁⁻¹ * w₁ := by group
      _ = (v * v) * w₁ := by rw [e, e2]
  have hw₁cz : w₁ * (v * v) ≠ t * t' := by
    intro he
    apply h.not_mem_P hw₁ hw₁z
    have : w₁ = (t * t') * (v * v)⁻¹ := by rw [← he]; group
    rw [this]
    exact mul_mem h.z_mem (inv_mem hcP)
  have hne1 : w₁ * (v * v) ≠ w₁ := fun he => hc1 (by simpa using he)
  have hcomm : w₁ * (w₁ * (v * v)) = (w₁ * (v * v)) * w₁ := by
    rw [mul_assoc, hcw, mul_assoc]
  have hceq := h.eq_z_mul_of_comm hw₁S hw₁ hw₁z (mul_mem hw₁S (mul_mem hvS hvS))
    (hw₁.trans hconjc) hw₁cz hcomm hne1
  have hzw : (t * t') * w₁ = w₁ * (t * t') := (h.comm_z hw₁S).symm
  have hvvz : v * v = t * t' := by
    rw [hzw] at hceq
    exact mul_left_cancel hceq
  have hvt : v * t = t * v := mem_centralizer_singleton_iff.mp (h.hPC hvP)
  have hvinv : v⁻¹ = v * (t * t') := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, hvvz, h.z_sq]
  have htw : t * w₁ * t⁻¹ = (t * t') * w₁ := h.conj_t_w hw₁S hw₁ hw₁z
  have hvw2 : v * w₁ = w₁ * v⁻¹ := by
    have e : w₁ * v⁻¹ * w₁⁻¹ = v := by
      rw [show w₁ * v⁻¹ * w₁⁻¹ = (w₁ * v * w₁⁻¹)⁻¹ by group, hvw, inv_inv]
    calc v * w₁ = w₁ * v⁻¹ * w₁⁻¹ * w₁ := by rw [e]
      _ = w₁ * v⁻¹ := by group
  have hconj1 : v * w₁ * v⁻¹ = w₁ * (t * t') := by
    calc v * w₁ * v⁻¹ = w₁ * (v * v)⁻¹ := by rw [hvw2]; group
      _ = w₁ * (t * t') := by rw [hvvz, inv_eq_of_mul_eq_one_right h.z_sq]
  have hsw : (t * v) * w₁ * (t * v)⁻¹ = w₁ := by
    calc (t * v) * w₁ * (t * v)⁻¹ = t * (v * w₁ * v⁻¹) * t⁻¹ := by group
      _ = t * (w₁ * (t * t')) * t⁻¹ := by rw [hconj1]
      _ = (t * w₁ * t⁻¹) * (t * (t * t') * t⁻¹) := by group
      _ = ((t * t') * w₁) * (t * t') := by rw [htw, h.conj_z h.t_mem_S]
      _ = w₁ := by rw [hzw, mul_assoc, h.z_sq, mul_one]
  have hscomm : (t * v) * w₁ = w₁ * (t * v) := by
    calc (t * v) * w₁ = (t * v) * w₁ * (t * v)⁻¹ * (t * v) := by group
      _ = w₁ * (t * v) := by rw [hsw]
  have hss : (t * v) * (t * v) = t * t' := by
    calc (t * v) * (t * v) = t * (v * t) * v := by group
      _ = t * (t * v) * v := by rw [hvt]
      _ = (t * t) * (v * v) := by group
      _ = t * t' := by rw [h.t_sq, one_mul, hvvz]
  obtain ⟨g₁, hg₁, hS₁⟩ := h.exists_conj_sylow hw₁
  have hs1 := hS₁ (t * v) (mul_mem h.t_mem_S hvS) hscomm
  have hsq := h.mul_self_mem_P hs1
  have e : g₁⁻¹ * (t * v) * g₁ * (g₁⁻¹ * (t * v) * g₁) = g₁⁻¹ * (t * t') * g₁ := by
    rw [← hss]
    group
  rw [e] at hsq
  have he := h.eq_z_of_mem (isConj_iff.mpr ⟨g₁⁻¹, by group⟩) hsq
  apply hw₁z
  calc w₁ = g₁ * (t * t') * g₁⁻¹ := hg₁.symm
    _ = g₁ * (g₁⁻¹ * (t * t') * g₁) * g₁⁻¹ := by rw [he]
    _ = t * t' := by group

theorem conj_mem_pair [Finite H] (h : Resid t t' P S) {w s : H} (hwS : w ∈ (S : Subgroup H))
    (hw : IsConj (t * t') w) (hwz : w ≠ t * t') (hs : s ∈ (S : Subgroup H)) :
    s * w * s⁻¹ = w ∨ s * w * s⁻¹ = (t * t') * w := by
  have hw'S : s * w * s⁻¹ ∈ (S : Subgroup H) := mul_mem (mul_mem hs hwS) (inv_mem hs)
  have hw' : IsConj (t * t') (s * w * s⁻¹) := hw.trans (isConj_conj w s)
  have hw'z : s * w * s⁻¹ ≠ t * t' := by
    intro he
    apply hwz
    calc w = s⁻¹ * (s * w * s⁻¹) * s⁻¹⁻¹ := by group
      _ = t * t' := by rw [he, h.conj_z (inv_mem hs)]
  by_cases he : s * w * s⁻¹ = w
  · exact Or.inl he
  · exact Or.inr (h.eq_z_mul_of_comm hwS hw hwz hw'S hw' hw'z
      (h.comm_of_mem hwS hw hwz hw'S hw' hw'z) he)

theorem relIndex_inf_centralizer [Finite H] (h : Resid t t' P S) {w : H}
    (hwS : w ∈ (S : Subgroup H)) (hw : IsConj (t * t') w) (hwz : w ≠ t * t') :
    ((S : Subgroup H) ⊓ centralizer ({w} : Set H)).relIndex (S : Subgroup H) = 2 := by
  have hmemT : ∀ b : (S : Subgroup H),
      b ∈ ((S : Subgroup H) ⊓ centralizer ({w} : Set H)).subgroupOf (S : Subgroup H) ↔
        (b : H) * w * (b : H)⁻¹ = w := by
    intro b
    rw [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, hb⟩
      rw [hb]
      group
    · intro hb
      refine ⟨b.2, ?_⟩
      calc (b : H) * w = (b : H) * w * (b : H)⁻¹ * b := by group
        _ = w * b := by rw [hb]
  have hzw : (t * t') * w ≠ w := fun he => h.z_ne_one (by simpa using he)
  rw [relIndex, index_eq_two_iff]
  refine ⟨⟨t, h.t_mem_S⟩, fun b => ?_⟩
  rw [hmemT, hmemT]
  have e : ((b * ⟨t, h.t_mem_S⟩ : (S : Subgroup H)) : H) * w *
      ((b * ⟨t, h.t_mem_S⟩ : (S : Subgroup H)) : H)⁻¹ = (t * t') * ((b : H) * w * (b : H)⁻¹) := by
    rw [Subgroup.coe_mul]
    calc (b : H) * t * w * ((b : H) * t)⁻¹ = (b : H) * (t * w * t⁻¹) * (b : H)⁻¹ := by group
      _ = (b : H) * ((t * t') * w) * (b : H)⁻¹ := by rw [h.conj_t_w hwS hw hwz]
      _ = ((b : H) * (t * t') * (b : H)⁻¹) * ((b : H) * w * (b : H)⁻¹) := by group
      _ = (t * t') * ((b : H) * w * (b : H)⁻¹) := by rw [h.conj_z b.2]
  rw [e]
  rcases h.conj_mem_pair hwS hw hwz b.2 with h1 | h1
  · rw [h1]
    exact Or.inr ⟨rfl, hzw⟩
  · rw [h1, ← mul_assoc, h.z_sq, one_mul]
    exact Or.inl ⟨rfl, hzw⟩

theorem not_mem_of_conj [Finite H] (h : Resid t t' P S) {w : H} (hwS : w ∈ (S : Subgroup H))
    (hw : IsConj (t * t') w) (hwz : w ≠ t * t') :
    t ∉ normalClosure ({t * t'} : Set H) := by
  have hQu : ∀ x : H, x⁻¹ * t * x ∉ (S : Subgroup H) ⊓ centralizer ({w} : Set H) := by
    rintro x ⟨hxS, hxw⟩
    exact h.not_comm hxS (isConj_iff.mpr ⟨x⁻¹, by group⟩) hwS hw hwz
      (mem_centralizer_singleton_iff.mp hxw)
  obtain ⟨N, hN, hsq, htN⟩ := Quasithin.thompson_transfer_exists_normal S inf_le_left
    (h.relIndex_inf_centralizer hwS hw hwz) h.ht hQu
  have hzN : t * t' ∈ N := by
    rw [← h.sq_t_mul hwS hw hwz]
    exact hsq _
  exact fun htm => htN (normalClosure_le_normal (Set.singleton_subset_iff.mpr hzN) htm)

end Resid

omit [Group H] in
theorem zpow_eq_one_or_self {G : Type*} [Group G] {x : G} (hx : x * x = 1) (k : ℤ) :
    x ^ k = 1 ∨ x ^ k = x := by
  have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [← Int.emod_add_mul_ediv k 2, hk, zero_add, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, hk, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]

theorem eq_one_of_mem_odd {N : Subgroup H} (hN : Odd (Nat.card N)) {x : H} (hxN : x ∈ N)
    (hx : x * x = 1) : x = 1 := by
  by_contra hx1
  have hd := N.orderOf_dvd_natCard hxN
  rw [orderOf_eq_two_of_mul_self hx hx1] at hd
  exact Nat.not_even_iff_odd.mpr hN (even_iff_two_dvd.mpr hd)

namespace Resid

variable {t t' : H} {P : Subgroup H} {S : Sylow 2 H}

theorem not_mem_of_isolated [Finite H] (h : Resid t t' P S)
    (hY : ∀ w ∈ (S : Subgroup H), IsConj (t * t') w → w = t * t') :
    t ∉ normalClosure ({t * t'} : Set H) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype H := Fintype.ofFinite H
  have hiso : ∀ g : H, (g * (t * t') * g⁻¹) * (t * t') = (t * t') * (g * (t * t') * g⁻¹) →
      g * (t * t') * g⁻¹ = t * t' := by
    intro g hg
    obtain ⟨k, hkC, hk⟩ := exists_conj_le_of_isSylowOf h.isSylowOf_S
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hg))
      (isPGroup_zpowers_of_mul_self (conj_mul_self h.z_sq g))
    have hmem := hk _ (mem_zpowers _)
    have he := hY _ hmem ((isConj_conj (t * t') g).trans (isConj_iff.mpr ⟨k⁻¹, by group⟩))
    have hkz : k * (t * t') = (t * t') * k := mem_centralizer_singleton_iff.mp hkC
    calc g * (t * t') * g⁻¹ = k * (k⁻¹ * (g * (t * t') * g⁻¹) * k) * k⁻¹ := by group
      _ = k * (t * t') * k⁻¹ := by rw [he]
      _ = t * t' := by rw [hkz]; group
  obtain ⟨N, hN, hNodd, hNz⟩ := ZStar.glauberman_zStar H (t * t') h.z_ne_one h.z_sq hiso
  set zbar := QuotientGroup.mk' N (t * t') with hzbar
  have hcen : ∀ g : H, (QuotientGroup.mk' N g) * zbar * (QuotientGroup.mk' N g)⁻¹ = zbar := by
    intro g
    rw [hzbar, ← map_inv, ← map_mul, ← map_mul]
    apply QuotientGroup.eq.mpr
    have hm := hN.conj_mem _ (inv_mem (hNz g)) (t * t')⁻¹
    have e : (g * (t * t') * g⁻¹)⁻¹ * (t * t') =
        (t * t')⁻¹ * (g * (t * t') * g⁻¹ * (t * t')⁻¹)⁻¹ * (t * t')⁻¹⁻¹ := by group
    rw [e]
    exact hm
  set K : Subgroup H := (zpowers zbar).comap (QuotientGroup.mk' N) with hK
  have hKn : K.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hK, mem_comap] at hx ⊢
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hx
    have e : QuotientGroup.mk' N (g * x * g⁻¹) =
        QuotientGroup.mk' N g * QuotientGroup.mk' N x * (QuotientGroup.mk' N g)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [e, ← hk, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hcen]
    exact zpow_mem (mem_zpowers _) k
  have hzK : t * t' ∈ K := by
    rw [hK, mem_comap]
    exact mem_zpowers _
  intro htm
  have htK : t ∈ K := normalClosure_le_normal (Set.singleton_subset_iff.mpr hzK) htm
  rw [hK, mem_comap] at htK
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp htK
  have hzz : QuotientGroup.mk' N (t * t') * QuotientGroup.mk' N (t * t') = 1 := by
    rw [← map_mul, h.z_sq, map_one]
  rcases zpow_eq_one_or_self hzz k with h1 | h1 <;> rw [h1] at hk
  ·
    have htN : t ∈ N := (QuotientGroup.eq_one_iff t).mp hk.symm
    exact h.t_ne_one (eq_one_of_mem_odd hNodd htN h.t_sq)
  ·
    have ht'N : t⁻¹ * (t * t') ∈ N := QuotientGroup.eq.mp hk.symm
    rw [← mul_assoc, inv_mul_cancel, one_mul] at ht'N
    have h1 : t' = 1 := eq_one_of_mem_odd hNodd ht'N h.t'_sq
    have h2 := h.isConj_t'
    rw [h1] at h2
    exact h.t_ne_one (eq_one_of_isConj_one h2.symm)

theorem not_mem [Finite H] (h : Resid t t' P S) : t ∉ normalClosure ({t * t'} : Set H) := by
  by_cases hY : ∃ w ∈ (S : Subgroup H), IsConj (t * t') w ∧ w ≠ t * t'
  · obtain ⟨w, hwS, hw, hwz⟩ := hY
    exact h.not_mem_of_conj hwS hw hwz
  · push Not at hY
    exact h.not_mem_of_isolated hY

end Resid

theorem mem_of_isSylowOf [Finite H] {t : H} {P : Subgroup H} (ht2 : t * t = 1)
    (hSyl : IsSylowOf 2 P (centralizer ({t} : Set H))) : t ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : P ≤ normalizer ((zpowers t : Subgroup H) : Set H) := by
    intro p hp
    have hpt : p * t = t * p := mem_centralizer_singleton_iff.mp (hSyl.le hp)
    have hconj : ∀ k : ℤ, p * t ^ k * p⁻¹ = t ^ k := fun k => by
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
      congr 1
      calc p * t * p⁻¹ = t * p * p⁻¹ := by rw [hpt]
        _ = t := by group
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
      rw [hconj]
      exact zpow_mem (mem_zpowers t) k
    · intro hx
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hx
      have e : x = t ^ k := by
        calc x = p⁻¹ * (p * x * p⁻¹) * p := by group
          _ = p⁻¹ * (p * t ^ k * p⁻¹) * p := by rw [← hk, hconj]
          _ = t ^ k := by group
      rw [e]
      exact zpow_mem (mem_zpowers t) k
  have hp : IsPGroup 2 ↥(P ⊔ zpowers t) :=
    hSyl.isPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_mul_self ht2) hnorm
  have hle : P ⊔ zpowers t ≤ centralizer ({t} : Set H) :=
    sup_le hSyl.le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
  rw [← hSyl.eq_of_le le_sup_left hle hp]
  exact mem_sup_right (mem_zpowers t)

theorem exists_sylow_relIndex_two [Finite H] {t t' : H} {P : Subgroup H} (ht : orderOf t = 2)
    (htt' : t ≠ t') (hSyl : IsSylowOf 2 P (centralizer ({t} : Set H)))
    (hP : ∀ x : H, (x ∈ P ∧ IsConj t x) ↔ x = t ∨ x = t')
    (h4 : ¬ 4 ∣ (centralizer ({t} : Set H)).index) :
    ∃ S : Sylow 2 H, P ≤ (S : Subgroup H) ∧ P.relIndex (S : Subgroup H) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPC := hSyl.le
  obtain ⟨-, hPp, hPodd⟩ := isSylowOf_iff.mp hSyl
  have h2P := two_dvd_index_of_two_conjugates ht htt' P hPC hP
  obtain ⟨S, hPS⟩ := hPp.exists_le_sylow
  refine ⟨S, hPS, ?_⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hdvd : P.relIndex (S : Subgroup H) ∣ 2 ^ n := by
    rw [← hn]
    exact (P.subgroupOf (S : Subgroup H)).index_dvd_card
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have e1 := relIndex_mul_index hPS
  have e2 := relIndex_mul_index hPC
  have hc2 : 2 ∣ (centralizer ({t} : Set H)).index := by
    rw [← e2] at h2P
    exact ((Nat.Prime.dvd_mul Nat.prime_two).mp h2P).resolve_left hPodd
  have hj1 := eq_one_of_two_pow_mul S.not_dvd_index hPodd hc2 h4 (by rw [← hj, e1, e2])
  rw [hj, hj1, pow_one]

end CFSG.ComponentClassification.Foote47

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ABGLocalTools

theorem footeThompsonFusion :
    ∀ (H : Type) [Group H] [Finite H] (t t' : H) (P : Subgroup H), orderOf t = 2 →
      IsSylowOf 2 P (centralizer ({t} : Set H)) → t' ∈ P →
      (∀ x ∈ P, IsConj t x ↔ x = t ∨ x = t') →
        t ∉ Subgroup.normalClosure ({t * t'} : Set H) := by
  intro H _ _ t t' P ht hSyl ht'P hconj
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htP : t ∈ P := Foote47.mem_of_isSylowOf ht2 hSyl
  have hP : ∀ x : H, (x ∈ P ∧ IsConj t x) ↔ x = t ∨ x = t' := by
    intro x
    constructor
    · rintro ⟨hx, hc⟩
      exact (hconj x hx).mp hc
    · rintro (rfl | rfl)
      · exact ⟨htP, IsConj.refl _⟩
      · exact ⟨ht'P, (hconj _ ht'P).mpr (Or.inr rfl)⟩
  by_cases htt' : t = t'
  · subst htt'
    rw [ht2]
    intro hmem
    have hle : normalClosure ({1} : Set H) ≤ ⊥ := normalClosure_le_normal (by simp)
    have h1 : t = 1 := mem_bot.mp (hle hmem)
    rw [h1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h4 : 4 ∣ (centralizer ({t} : Set H)).index
  · exact not_mem_normalClosure_of_four_dvd_index ht P hSyl.le (isSylowOf_iff.mp hSyl).2.2 hP h4
  obtain ⟨S, hPS, hidx⟩ := Foote47.exists_sylow_relIndex_two ht htt' hSyl hP h4
  exact Foote47.Resid.not_mem ⟨ht, htt', hSyl, hP, hPS, hidx⟩

theorem footeThompsonFusion_holds : FooteThompsonFusion := by
  intro H _ _ t t' ht P hP
  exact footeThompsonFusion H t t' _ ht ⟨P, rfl⟩ ((hP t').mpr (Or.inr rfl)).1
    fun x hx => ⟨fun hc => (hP x).mp ⟨hx, hc⟩, fun h => ((hP x).mpr h).2⟩

end CFSG.ComponentClassification.FooteLit
