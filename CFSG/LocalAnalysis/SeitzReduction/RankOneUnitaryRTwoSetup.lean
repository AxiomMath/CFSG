module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiPartitionBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRTwoBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

variable {G : Type*} [Group G]

structure U3RSetup (T₁ R₁ : Subgroup G) (t : G) (q : ℕ) : Prop where
  four_le : 4 ≤ q
  t_sq : t ^ 2 = 1
  t_comm : t ∈ centralizer (T₁ : Set G)
  t_not_mem : t ∉ T₁
  sq_T₁ : ∀ y ∈ T₁, y ^ 2 ∈ szA₁ T₁
  sq_A₁ : ∀ b ∈ szA₁ T₁, b ^ 2 = 1
  card_A₁ : Nat.card (szA₁ T₁) = q
  card_T₁ : Nat.card T₁ = q ^ 3
  card_R₁ : Nat.card R₁ = 2 * q ^ 4
  le_R₁ : T₁ ⊔ zpowers t ≤ R₁
  le_centralizer : R₁ ≤ centralizer (szA₁ T₁ : Set G)
  rho_mem : ∀ r ∈ R₁, r * t * r⁻¹ * t⁻¹ ∈ szA₁ T₁
  cover : ∀ b ∈ szA₁ T₁, ∃ r ∈ R₁, r * t * r⁻¹ = b * t
  inf_centralizer : R₁ ⊓ centralizer ({t} : Set G) = T₁ ⊔ zpowers t
  sq_mem : ∀ r ∈ R₁, r ^ 2 ∈ szA₁ T₁ ⊔ zpowers t

structure U3RTorus (T₁ R₁ : Subgroup G) (t d k : G) : Prop where
  odd : Odd (orderOf d)
  mem_normalizer_R₁ : d ∈ normalizer (R₁ : Set G)
  mem_normalizer_T₁ : d ∈ normalizer (T₁ : Set G)
  comm_t : d * t = t * d
  trans : ∀ b ∈ szA₁ T₁, ∀ b' ∈ szA₁ T₁, b ≠ 1 → b' ≠ 1 → ∃ n : ℕ, (d ^ n)⁻¹ * b * d ^ n = b'
  k_mem : k ∈ zpowers d
  k_centralizer : k ∈ centralizer (szA₁ T₁ : Set G)
  k_surj : ∀ y ∈ T₁, ∃ y' ∈ T₁, y⁻¹ * (k * y' * k⁻¹ * y'⁻¹) ∈ szA₁ T₁

namespace U3RSetup

variable {T₁ R₁ : Subgroup G} {t : G} {q : ℕ} (h : U3RSetup T₁ R₁ t q)
include h

theorem t_ne_one : t ≠ 1 := fun h1 => h.t_not_mem (h1 ▸ one_mem _)

theorem orderOf_t : orderOf t = 2 := orderOf_eq_prime h.t_sq h.t_ne_one

theorem t_inv : t⁻¹ = t := by
  rw [inv_eq_iff_mul_eq_one, ← sq, h.t_sq]

theorem disj : T₁ ⊓ zpowers t = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxT, hxt⟩ := mem_inf.mp hx
  rcases mem_zpowers_involution_eq_one_or_eq h.t_sq hxt with rfl | rfl
  · exact one_mem _
  · exact absurd hxT h.t_not_mem

theorem T₁_le_R₁ : T₁ ≤ R₁ := le_sup_left.trans h.le_R₁

theorem t_mem_R₁ : t ∈ R₁ := h.le_R₁ (mem_sup_right (mem_zpowers t))

theorem szA₁_le_R₁ : szA₁ T₁ ≤ R₁ := (szA₁_le T₁).trans h.T₁_le_R₁

omit h in
theorem szA₁_le_sup : szA₁ T₁ ≤ T₁ ⊔ zpowers t := (szA₁_le T₁).trans le_sup_left

theorem t_mem_centralizer_szA₁ : t ∈ centralizer (szA₁ T₁ : Set G) :=
  centralizer_le (szA₁_le T₁) h.t_comm

omit h in
theorem szA₁_comm {b b' : G} (hb : b ∈ szA₁ T₁) (hb' : b' ∈ szA₁ T₁) : b * b' = b' * b :=
  mem_centralizer_iff.mp (mem_szA₁.mp hb').2 b (szA₁_le T₁ hb)

theorem szA₁_comm_R₁ {b r : G} (hb : b ∈ szA₁ T₁) (hr : r ∈ R₁) : b * r = r * b :=
  mem_centralizer_iff.mp (h.le_centralizer hr) b hb

theorem card_sup : Nat.card (T₁ ⊔ zpowers t : Subgroup G) = 2 * q ^ 3 := by
  rw [card_sup_zpowers_of_disjoint h.t_comm h.orderOf_t h.disj, h.card_T₁, mul_comm]

theorem sq_mem_szA₁ {r : G} (hr : r ∈ R₁) : r ^ 2 ∈ szA₁ T₁ := by
  rcases SzPartition.mem_sup_zpowers_cases h.t_mem_centralizer_szA₁ h.t_sq (h.sq_mem r hr) with
    h1 | ⟨b, hb, hrb⟩
  · exact h1
  exfalso
  obtain ⟨x, hx, hxt⟩ := h.cover b hb
  have hyR : x⁻¹ * r * x ∈ R₁ := mul_mem (mul_mem (inv_mem hx) hr) hx
  have hy2 : (x⁻¹ * r * x) ^ 2 = t := by
    calc (x⁻¹ * r * x) ^ 2 = x⁻¹ * r ^ 2 * x := by rw [sq, sq]; group
      _ = x⁻¹ * (x * t * x⁻¹) * x := by rw [hrb, hxt]
      _ = t := by group
  have hyt : x⁻¹ * r * x ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff, ← hy2]
    exact (Commute.self_pow _ 2).eq
  have hyW : x⁻¹ * r * x ∈ T₁ ⊔ zpowers t := by
    rw [← h.inf_centralizer]
    exact mem_inf.mpr ⟨hyR, hyt⟩
  obtain ⟨y₁, hy₁, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.t_comm hyW
  have hy₁z : Commute y₁ z :=
    commute_of_mem_zpowers hz (mem_centralizer_iff.mp h.t_comm y₁ hy₁)
  have hz2 : z ^ 2 = 1 := by
    rcases mem_zpowers_involution_eq_one_or_eq h.t_sq hz with rfl | rfl
    · exact one_pow 2
    · exact h.t_sq
  have htA : t ∈ szA₁ T₁ := by
    rw [← hy2, ← hyz, hy₁z.mul_pow, hz2, mul_one]
    exact h.sq_T₁ y₁ hy₁
  exact h.t_not_mem (szA₁_le T₁ htA)

theorem comm_mem_szA₁ {r r' : G} (hr : r ∈ R₁) (hr' : r' ∈ R₁) :
    r * r' * r⁻¹ * r'⁻¹ ∈ szA₁ T₁ := by
  refine comm_mem_of_sq_mem_of_conj_mem (fun n hn => ?_) (h.sq_mem_szA₁ hr) (h.sq_mem_szA₁ hr')
    (h.sq_mem_szA₁ (mul_mem hr hr'))
  rw [mul_assoc, h.szA₁_comm_R₁ hn hr', inv_mul_cancel_left]
  exact hn

theorem conj_mem_sup {r w : G} (hr : r ∈ R₁) (hw : w ∈ T₁ ⊔ zpowers t) :
    r * w * r⁻¹ ∈ T₁ ⊔ zpowers t := by
  have h1 := h.comm_mem_szA₁ hr (h.le_R₁ hw)
  have e : r * w * r⁻¹ = (r * w * r⁻¹ * w⁻¹) * w := by group
  rw [e]
  exact mul_mem (szA₁_le_sup h1) hw

theorem le_normalizer_sup : R₁ ≤ normalizer ((T₁ ⊔ zpowers t : Subgroup G) : Set G) := by
  intro r hr
  refine mem_normalizer_iff.mpr fun w => ⟨fun hw => h.conj_mem_sup hr hw, fun hw => ?_⟩
  have := h.conj_mem_sup (inv_mem hr) hw
  rwa [show r⁻¹ * (r * w * r⁻¹) * r⁻¹⁻¹ = w by group] at this

theorem rho_mul {r r' : G} (hr : r ∈ R₁) (hr' : r' ∈ R₁) :
    r * r' * t * (r * r')⁻¹ * t⁻¹ = (r * t * r⁻¹ * t⁻¹) * (r' * t * r'⁻¹ * t⁻¹) := by
  have hc := h.szA₁_comm_R₁ (h.rho_mem r' hr') hr
  have hab := szA₁_comm (h.rho_mem r hr) (h.rho_mem r' hr')
  rw [hab]
  calc r * r' * t * (r * r')⁻¹ * t⁻¹ = r * (r' * t * r'⁻¹ * t⁻¹) * t * r⁻¹ * t⁻¹ := by group
    _ = (r' * t * r'⁻¹ * t⁻¹) * r * t * r⁻¹ * t⁻¹ := by rw [← hc]
    _ = (r' * t * r'⁻¹ * t⁻¹) * (r * t * r⁻¹ * t⁻¹) := by group

theorem rho_eq_one_iff {r : G} (hr : r ∈ R₁) :
    r * t * r⁻¹ * t⁻¹ = 1 ↔ r ∈ T₁ ⊔ zpowers t := by
  rw [← h.inf_centralizer, mem_inf, mem_centralizer_singleton_iff]
  constructor
  · intro h1
    refine ⟨hr, ?_⟩
    calc r * t = r * t * r⁻¹ * t⁻¹ * (t * r) := by group
      _ = t * r := by rw [h1, one_mul]
  · rintro ⟨-, h1⟩
    rw [h1, mul_inv_cancel_right, mul_inv_cancel]

end U3RSetup

end CFSG.SeitzReduction.RankOne
