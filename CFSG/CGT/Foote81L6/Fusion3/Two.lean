module

public import CFSG.CGT.Foote81L6.Fusion3.Sylow
public import CFSG.CGT.Foote81L6.Fusion3.Zab
public import CFSG.CGT.Foote81L6.Normalizer.GAzero

public section

namespace CFSG.CGT.Foote81L6.Fusion3

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {n : ℕ}
  (D : FooteCore G (T : Subgroup G) 2 n)

theorem comm_of_mem_A_of_mem_T₀ {α v : G} (hα : α ∈ D.A) (hv : v ∈ D.T₀) : v * α = α * v := by
  obtain ⟨x, hx, y, hy, rfl⟩ := D.mem_T₀_iff.1 hv
  have h1 : x * α = α * x := D.A_comm_of_two hx hα
  have h2 : y * α = α * y := (D.A_comm_B α hα y hy).symm
  calc x * y * α = x * (y * α) := mul_assoc _ _ _
    _ = x * (α * y) := by rw [h2]
    _ = (x * α) * y := (mul_assoc _ _ _).symm
    _ = (α * x) * y := by rw [h1]
    _ = α * (x * y) := mul_assoc _ _ _

theorem conj_b_of_mem_normalizer_T₀ {k : G} (hk : k ∈ normalizer (D.T₀ : Set G)) :
    k * D.b * k⁻¹ = D.b := by
  obtain ⟨y, hy, hyy⟩ := D.exists_mul_self_eq_b
  have hyT₀ : k * y * k⁻¹ ∈ D.T₀ := (mem_normalizer_iff.1 hk y).1 (D.B_le_T₀ (D.B₀B₁_le_B hy))
  obtain ⟨α, hα, β, hβ, hαβ⟩ := D.mem_T₀_iff.1 hyT₀
  have hsq : k * D.b * k⁻¹ = β * β := by
    calc k * D.b * k⁻¹ = (k * y * k⁻¹) * (k * y * k⁻¹) := by rw [← hyy]; group
      _ = α * β * (α * β) := by rw [hαβ]
      _ = (α * α) * (β * β) := by
          rw [mul_assoc α β, ← mul_assoc β α, ← D.A_comm_B α hα β hβ]
          group
      _ = β * β := by rw [D.mul_self_of_two hα, one_mul]
  have hcomm : ∀ v ∈ D.B, v * (k * D.b * k⁻¹) = (k * D.b * k⁻¹) * v := by
    intro v hv
    have hv' : k⁻¹ * v * k ∈ D.T₀ := by
      have := (mem_normalizer_iff.1 (inv_mem hk) v).1 (D.B_le_T₀ hv)
      rwa [inv_inv] at this
    have hc : (k⁻¹ * v * k) * D.b = D.b * (k⁻¹ * v * k) := D.b_comm_T (D.T₀_le_T hv')
    calc v * (k * D.b * k⁻¹) = k * ((k⁻¹ * v * k) * D.b) * k⁻¹ := by group
      _ = k * (D.b * (k⁻¹ * v * k)) * k⁻¹ := by rw [hc]
      _ = (k * D.b * k⁻¹) * v := by group
  rcases D.eq_one_or_b_of_comm_B (hsq ▸ mul_mem hβ hβ) hcomm with h | h
  · exact absurd (conj_eq_one_iff.1 h) D.b_ne_one
  · exact h

theorem conj_eq_of_mem_ab (hcen : D.a ∈ center G) {k : G} (hk : k ∈ normalizer (D.T₀ : Set G))
    {c : G} (hc : c = 1 ∨ c = D.a ∨ c = D.b ∨ c = D.a * D.b) : k * c * k⁻¹ = c := by
  have ha : k * D.a * k⁻¹ = D.a := by rw [mem_center_iff.1 hcen k, mul_inv_cancel_right]
  have hb := conj_b_of_mem_normalizer_T₀ D hk
  rcases hc with rfl | rfl | rfl | rfl
  · group
  · exact ha
  · exact hb
  · calc k * (D.a * D.b) * k⁻¹ = (k * D.a * k⁻¹) * (k * D.b * k⁻¹) := by group
      _ = D.a * D.b := by rw [ha, hb]

theorem mem_T_of_mem_ab {c : G} (hc : c = 1 ∨ c = D.a ∨ c = D.b ∨ c = D.a * D.b) :
    c ∈ (T : Subgroup G) := by
  rcases hc with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact D.a_mem_T
  · exact D.b_mem_T
  · exact mul_mem D.a_mem_T D.b_mem_T

include D in
private theorem eq_one_of_mem_A_of_mem_B {x : G} (hxA : x ∈ D.A) (hxB : x ∈ D.B) : x = 1 := by
  have h : x ∈ D.A ⊓ D.B := mem_inf.2 ⟨hxA, hxB⟩
  rwa [D.A_inf_B, mem_bot] at h

theorem eq_or_eq_of_mem_A {a₁ α : G} (ha₁ : a₁ ∈ D.A) (ha₁1 : a₁ ≠ 1) (ha₁a : a₁ ≠ D.a)
    (hα : α ∈ D.A) (hα1 : α ≠ 1) (hαa : α ≠ D.a) : α = a₁ ∨ α = a₁ * D.a := by
  have ht₁ := Normalizer.conj_t_of_mem_A D ha₁ ha₁1 ha₁a
  have htα := Normalizer.conj_t_of_mem_A D hα hα1 hαa
  have hβA : a₁⁻¹ * α ∈ D.A := mul_mem (inv_mem ha₁) hα
  have hβt : (a₁⁻¹ * α) * D.t = D.t * (a₁⁻¹ * α) := by
    have e : D.t * (a₁⁻¹ * α) * D.t⁻¹ = a₁⁻¹ * α := by
      calc D.t * (a₁⁻¹ * α) * D.t⁻¹ = (D.t * a₁ * D.t⁻¹)⁻¹ * (D.t * α * D.t⁻¹) := by group
        _ = a₁⁻¹ * α := by rw [ht₁, htα]; group
    exact comm_of_conj_eq e
  rcases D.eq_one_or_a_of_comm_t hβA hβt with h | h
  · left
    calc α = a₁ * (a₁⁻¹ * α) := by group
      _ = a₁ := by rw [h, mul_one]
  · right
    calc α = a₁ * (a₁⁻¹ * α) := by group
      _ = a₁ * D.a := by rw [h]

theorem exists_conj_a₁_eq (hcen : D.a ∈ center G) {a₁ : G} (ha₁ : a₁ ∈ D.A) (ha₁1 : a₁ ≠ 1)
    (ha₁a : a₁ ≠ D.a) {k : G} (hk : k ∈ normalizer (D.T₀ : Set G)) :
    ∃ c : G, (c = 1 ∨ c = D.a ∨ c = D.b ∨ c = D.a * D.b) ∧ k * a₁ * k⁻¹ = a₁ * c := by
  have hzT₀ : k * a₁ * k⁻¹ ∈ D.T₀ := (mem_normalizer_iff.1 hk a₁).1 (D.A_le_T₀ ha₁)
  have hzc : ∀ v ∈ D.T₀, v * (k * a₁ * k⁻¹) = (k * a₁ * k⁻¹) * v := by
    intro v hv
    have hv' : k⁻¹ * v * k ∈ D.T₀ := by
      have := (mem_normalizer_iff.1 (inv_mem hk) v).1 hv
      rwa [inv_inv] at this
    have hc := comm_of_mem_A_of_mem_T₀ D ha₁ hv'
    calc v * (k * a₁ * k⁻¹) = k * ((k⁻¹ * v * k) * a₁) * k⁻¹ := by group
      _ = k * (a₁ * (k⁻¹ * v * k)) * k⁻¹ := by rw [hc]
      _ = (k * a₁ * k⁻¹) * v := by group
  obtain ⟨α, hα, β, hβ, hαβ⟩ := D.mem_T₀_iff.1 hzT₀
  have hβc : ∀ v ∈ D.B, v * β = β * v := by
    intro v hv
    have h1 := hzc v (D.B_le_T₀ hv)
    rw [hαβ] at h1
    have h2 : α * v = v * α := D.A_comm_B α hα v hv
    have : α * (v * β) = α * (β * v) := by
      calc α * (v * β) = (v * α) * β := by rw [← mul_assoc, h2]
        _ = v * (α * β) := mul_assoc _ _ _
        _ = α * β * v := h1
        _ = α * (β * v) := mul_assoc _ _ _
    exact mul_left_cancel this
  have hβ' := D.eq_one_or_b_of_comm_B hβ hβc
  have hαab : ¬ (α = 1 ∨ α = D.a) := by
    rintro hα'
    have hz : α * β = 1 ∨ α * β = D.a ∨ α * β = D.b ∨ α * β = D.a * D.b := by
      rcases hα' with rfl | rfl <;> rcases hβ' with rfl | rfl
      · left; group
      · right; right; left; group
      · right; left; group
      · right; right; right; rfl
    have hfix := conj_eq_of_mem_ab D hcen (inv_mem hk) hz
    have ha₁z : a₁ = α * β := by
      rw [← hαβ] at hfix ⊢
      calc a₁ = k⁻¹ * (k * a₁ * k⁻¹) * k⁻¹⁻¹ := by group
        _ = k * a₁ * k⁻¹ := hfix
    rcases hz with h | h | h | h <;> rw [h] at ha₁z
    · exact ha₁1 ha₁z
    · exact ha₁a ha₁z
    · exact D.b_ne_one (eq_one_of_mem_A_of_mem_B D (ha₁z ▸ ha₁) D.b_mem_B)
    · apply D.b_ne_one
      refine eq_one_of_mem_A_of_mem_B D ?_ D.b_mem_B
      have : D.b = D.a⁻¹ * a₁ := by rw [ha₁z]; group
      rw [this]
      exact mul_mem (inv_mem D.a_mem) ha₁
  push Not at hαab
  rcases eq_or_eq_of_mem_A D ha₁ ha₁1 ha₁a hα hαab.1 hαab.2 with rfl | rfl <;>
    rcases hβ' with rfl | rfl
  · exact ⟨1, Or.inl rfl, by rw [hαβ]⟩
  · exact ⟨D.b, Or.inr (Or.inr (Or.inl rfl)), hαβ⟩
  · exact ⟨D.a, Or.inr (Or.inl rfl), by rw [hαβ, mul_one]⟩
  · exact ⟨D.a * D.b, Or.inr (Or.inr (Or.inr rfl)), by rw [hαβ, mul_assoc]⟩

theorem conj_a₁_of_mem_T {a₁ : G} (ha₁ : a₁ ∈ D.A) (ha₁1 : a₁ ≠ 1) (ha₁a : a₁ ≠ D.a) {u : G}
    (hu : u ∈ (T : Subgroup G)) : u * a₁ * u⁻¹ = a₁ ∨ u * a₁ * u⁻¹ = D.a * a₁ := by
  rcases D.mem_T_iff.1 hu with h | h
  · left
    rw [comm_of_mem_A_of_mem_T₀ D ha₁ h, mul_inv_cancel_right]
  · right
    have ht : D.t⁻¹ * a₁ * D.t = D.a * a₁ := by
      rw [D.t_inv, ← Normalizer.conj_t_of_mem_A D ha₁ ha₁1 ha₁a, D.t_inv]
    have hc := comm_of_mem_A_of_mem_T₀ D (mul_mem D.a_mem ha₁) h
    calc u * a₁ * u⁻¹ = (u * D.t) * (D.t⁻¹ * a₁ * D.t) * (u * D.t)⁻¹ := by group
      _ = (u * D.t) * (D.a * a₁) * (u * D.t)⁻¹ := by rw [ht]
      _ = D.a * a₁ := by rw [hc, mul_inv_cancel_right]

theorem exists_mem_normalizer_T₀ (hcen : D.a ∈ center G) {a₁ : G} (ha₁ : a₁ ∈ D.A)
    (ha₁1 : a₁ ≠ 1) (ha₁a : a₁ ≠ D.a) {g : G} (hg : g * a₁ * g⁻¹ = a₁ * D.b) :
    ∃ k ∈ normalizer (D.T₀ : Set G), k * a₁ * k⁻¹ = a₁ * D.b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT₀2 : IsPGroup 2 D.T₀ := IsPGroup.of_card D.card_T₀
  have hT₀C : D.T₀ ≤ centralizer ({a₁ * D.b} : Set G) := fun v hv => by
    rw [mem_centralizer_singleton_iff]
    have h1 := comm_of_mem_A_of_mem_T₀ D ha₁ hv
    have h2 : v * D.b = D.b * v := D.b_comm_T (D.T₀_le_T hv)
    calc v * (a₁ * D.b) = (v * a₁) * D.b := (mul_assoc _ _ _).symm
      _ = (a₁ * v) * D.b := by rw [h1]
      _ = a₁ * (v * D.b) := mul_assoc _ _ _
      _ = a₁ * (D.b * v) := by rw [h2]
      _ = a₁ * D.b * v := (mul_assoc _ _ _).symm
  obtain ⟨h, hh, hhT₀⟩ := exists_conj_eq_and_conj_le hg
    (D.sylow_centralizer_A hcen ha₁ ha₁1 ha₁a) hT₀2 hT₀C
  have hN : h⁻¹ ∈ normalizer (D.T₀ : Set G) :=
    TStruct.mem_normalizer_of_forall_conj_mem fun v hv => by
      rw [inv_inv]
      exact hhT₀ v hv
  exact ⟨h, by simpa using inv_mem hN, hh⟩

theorem not_isConj_a₁_mul_b (hcen : D.a ∈ center G) {a₁ : G} (ha₁ : a₁ ∈ D.A) (ha₁1 : a₁ ≠ 1)
    (ha₁a : a₁ ≠ D.a) : ¬ IsConj a₁ (a₁ * D.b) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hconj
  obtain ⟨g, hg⟩ := isConj_iff.1 hconj
  obtain ⟨k, hkN, hk⟩ := exists_mem_normalizer_T₀ D hcen ha₁ ha₁1 ha₁a hg
  obtain ⟨e, r, hr, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
  have hkb : k * D.b * k⁻¹ = D.b := conj_b_of_mem_normalizer_T₀ D hkN
  have hkbj : ∀ j : ℕ, k ^ j * D.b * (k ^ j)⁻¹ = D.b := fun j => by
    have hcomm : Commute k D.b := (comm_of_conj_eq hkb).symm
    rw [(hcomm.pow_left j).eq, mul_inv_cancel_right]
  have hpow : ∀ j : ℕ, k ^ j * a₁ * (k ^ j)⁻¹ = a₁ * D.b ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc k ^ (j + 1) * a₁ * (k ^ (j + 1))⁻¹ = k ^ j * (k * a₁ * k⁻¹) * (k ^ j)⁻¹ := by group
        _ = (k ^ j * a₁ * (k ^ j)⁻¹) * (k ^ j * D.b * (k ^ j)⁻¹) := by rw [hk]; group
        _ = a₁ * D.b ^ (j + 1) := by rw [ih, hkbj j, pow_succ, mul_assoc]
  have hya : k ^ r * a₁ * (k ^ r)⁻¹ = a₁ * D.b := by
    obtain ⟨j, hj⟩ := hr
    have hb2 : D.b ^ 2 = 1 := by rw [sq]; exact D.b_mul_b
    rw [hpow r, hj, pow_succ, pow_mul, hb2, one_pow, one_mul]
  have hyN : k ^ r ∈ normalizer (D.T₀ : Set G) := pow_mem hkN r
  have hy2 : orderOf (k ^ r) = 2 ^ e := by
    rw [orderOf_pow_of_dvd hr.pos.ne' (Dvd.intro_left _ hord.symm), hord,
      Nat.mul_div_cancel _ hr.pos]
  have hTN : (T : Subgroup G) ≤ normalizer (D.T₀ : Set G) := D.T_le_normalizer_T₀
  have hP : IsPGroup 2 (zpowers (⟨k ^ r, hyN⟩ : ↥(normalizer (D.T₀ : Set G)))) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, orderOf_mk, hy2])
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥(normalizer (D.T₀ : Set G)) S (T.subtype hTN)
  have hmem : c * ⟨k ^ r, hyN⟩ * c⁻¹ ∈ ((T.subtype hTN : Sylow 2 _) : Subgroup _) := by
    rw [← hc, Sylow.coe_subgroup_smul, mem_smul_pointwise_iff_exists]
    exact ⟨_, hS (mem_zpowers _), rfl⟩
  rw [Sylow.coe_subtype, mem_subgroupOf] at hmem
  simp only [coe_mul, coe_inv] at hmem
  obtain ⟨c₁, hc₁, hc₁e⟩ := exists_conj_a₁_eq D hcen ha₁ ha₁1 ha₁a (inv_mem c.2)
  have hyc₁ : k ^ r * c₁ * (k ^ r)⁻¹ = c₁ := conj_eq_of_mem_ab D hcen hyN hc₁
  have hcc₁ : (c : G) * c₁ * (c : G)⁻¹ = c₁ := conj_eq_of_mem_ab D hcen c.2 hc₁
  have hcb : (c : G) * D.b * (c : G)⁻¹ = D.b := conj_b_of_mem_normalizer_T₀ D c.2
  have hc₁b : c₁ * D.b = D.b * c₁ := D.b_comm_T (mem_T_of_mem_ab D hc₁)
  have hca₁ : (c : G) * a₁ * (c : G)⁻¹ = a₁ * c₁⁻¹ := by
    have h1 : a₁ = ((c : G) * a₁ * (c : G)⁻¹) * c₁ := by
      calc a₁ = (c : G) * ((c : G)⁻¹ * a₁ * ((c : G)⁻¹)⁻¹) * (c : G)⁻¹ := by group
        _ = (c : G) * (a₁ * c₁) * (c : G)⁻¹ := by rw [hc₁e]
        _ = ((c : G) * a₁ * (c : G)⁻¹) * ((c : G) * c₁ * (c : G)⁻¹) := by group
        _ = ((c : G) * a₁ * (c : G)⁻¹) * c₁ := by rw [hcc₁]
    calc (c : G) * a₁ * (c : G)⁻¹ = ((c : G) * a₁ * (c : G)⁻¹) * c₁ * c₁⁻¹ := by group
      _ = a₁ * c₁⁻¹ := by rw [← h1]
  have hua : ((c : G) * k ^ r * (c : G)⁻¹) * a₁ * ((c : G) * k ^ r * (c : G)⁻¹)⁻¹ =
      a₁ * D.b := by
    calc ((c : G) * k ^ r * (c : G)⁻¹) * a₁ * ((c : G) * k ^ r * (c : G)⁻¹)⁻¹
        = (c : G) * (k ^ r * ((c : G)⁻¹ * a₁ * ((c : G)⁻¹)⁻¹) * (k ^ r)⁻¹) * (c : G)⁻¹ := by
          group
      _ = (c : G) * (k ^ r * (a₁ * c₁) * (k ^ r)⁻¹) * (c : G)⁻¹ := by rw [hc₁e]
      _ = (c : G) * ((k ^ r * a₁ * (k ^ r)⁻¹) * (k ^ r * c₁ * (k ^ r)⁻¹)) * (c : G)⁻¹ := by
          group
      _ = (c : G) * (a₁ * D.b * c₁) * (c : G)⁻¹ := by rw [hya, hyc₁]
      _ = ((c : G) * a₁ * (c : G)⁻¹) * ((c : G) * D.b * (c : G)⁻¹) *
          ((c : G) * c₁ * (c : G)⁻¹) := by group
      _ = a₁ * c₁⁻¹ * D.b * c₁ := by rw [hca₁, hcb, hcc₁]
      _ = a₁ * D.b := by rw [mul_assoc (a₁ * c₁⁻¹), ← hc₁b]; group
  rcases conj_a₁_of_mem_T D ha₁ ha₁1 ha₁a hmem with h | h
  · rw [hua] at h
    exact D.b_ne_one (mul_left_cancel (h.trans (mul_one a₁).symm))
  · rw [hua, ← D.A_comm_of_two ha₁ D.a_mem] at h
    have hba : D.b = D.a := mul_left_cancel h
    exact D.a_ne_one (eq_one_of_mem_A_of_mem_B D D.a_mem (hba ▸ D.b_mem_B))

theorem lemma3_two (hcen : D.a ∈ center G) {a₁ : G} (ha₁ : a₁ ∈ D.A) (ha₁1 : a₁ ≠ 1)
    (ha₁a : a₁ ≠ D.a) : ¬ IsConj a₁ (a₁ * D.b) ∧ ¬ IsConj a₁ (D.a * a₁ * D.b) := by
  have h1 := not_isConj_a₁_mul_b D hcen ha₁ ha₁1 ha₁a
  refine ⟨h1, fun h => h1 (h.trans (isConj_iff.2 ⟨D.t, ?_⟩))⟩
  have hta : D.t * D.a * D.t⁻¹ = D.a := by rw [D.a_comm_T D.t_mem_T, mul_inv_cancel_right]
  calc D.t * (D.a * a₁ * D.b) * D.t⁻¹
      = (D.t * D.a * D.t⁻¹) * (D.t * a₁ * D.t⁻¹) * (D.t * D.b * D.t⁻¹) := by group
    _ = D.a * (D.a * a₁) * D.b := by
        rw [hta, Normalizer.conj_t_of_mem_A D ha₁ ha₁1 ha₁a, D.conj_t_b]
    _ = a₁ * D.b := by rw [← mul_assoc, D.a_mul_a, one_mul]

end CFSG.CGT.Foote81L6.Fusion3
