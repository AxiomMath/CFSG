module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1PushUpAbelian
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryStart

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem sign_of_cartan (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {D : Subgroup G} {d : G}
    (hdD : d ∈ D) (hDN : D ≤ normalizer (szT₁ L T : Set G)) (hDodd : Odd (Nat.card D))
    (htr : ∀ b ∈ szA₁ (szT₁ L T), ∀ b' ∈ szA₁ (szT₁ L T), b ≠ 1 → b' ≠ 1 →
      ∃ n : ℕ, (d ^ n)⁻¹ * b * d ^ n = b')
    (hTD : ∀ s ∈ T, ∃ n ∈ szT₁ L T, ∀ x ∈ D, (n⁻¹ * s) * x * (n⁻¹ * s)⁻¹ ∈ D)
    {V : Subgroup G} (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hVT₁ : V ≤ centralizer (szT₁ L T : Set G)) {e : ℕ} (he : 2 ≤ e)
    (hcard : Nat.card V = (2 ^ f) ^ e) (hpow : ∀ x ∈ V, x ^ 2 ^ e = 1)
    (hΩ : ∀ x ∈ V, x ^ 2 = 1 → x ∈ szA₁ (szT₁ L T)) (hDV : D ≤ normalizer (V : Set G))
    (hTV : T ≤ normalizer (V : Set G)) {w : G} (hwT : w ∈ T) (hw2 : w ^ 2 = 1)
    (hwS : w ∉ szT₁ L T ⊔ zpowers t) :
    (∀ u ∈ V, w * u * w⁻¹ = u → u ∈ szA₁ (szT₁ L T)) ∨
      ∀ u ∈ V, u⁻¹ * (w * u * w⁻¹) ∈ szA₁ (szT₁ L T) := by
  obtain ⟨-, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨-, hwA, -, -⟩ := h.outer_facts_of_card_sylow hS2 hwT hw2 hwS
  obtain ⟨n, hn, hnD⟩ := hTD w hwT
  set m := n⁻¹ * w with hm
  have hnT : n ∈ T := szT₁_le_left L T hn
  have hmT : m ∈ T := mul_mem (inv_mem hnT) hwT
  have hmV : m ∈ normalizer (V : Set G) := hTV hmT
  have hdV : d ∈ normalizer (V : Set G) := hDV hdD
  have hwV : w ∈ normalizer (V : Set G) := hTV hwT
  have hdA : d ∈ normalizer (szA₁ (szT₁ L T) : Set G) :=
    normalizer_le_normalizer_inf_centralizer (szT₁ L T) (hDN hdD)
  have hwA' : ∀ b ∈ szA₁ (szT₁ L T), w * b * w⁻¹ = b := fun b hb => by
    rw [mul_inv_eq_iff_eq_mul]; exact hwA b hb
  have hnA : ∀ b ∈ szA₁ (szT₁ L T), n⁻¹ * b * n = b := fun b hb => by
    have h1 : n * b = b * n := mem_centralizer_iff.mp (mem_szA₁.mp hb).2 n hn
    rw [mul_assoc, ← h1, inv_mul_cancel_left]
  have hmA : ∀ b ∈ szA₁ (szT₁ L T), m⁻¹ * b * m = b := fun b hb => by
    have h1 : w⁻¹ * b * w = b := by
      have := hwA' b hb
      calc w⁻¹ * b * w = w⁻¹ * (w * b * w⁻¹) * w := by rw [this]
        _ = b := by group
    have h2 : n * b * n⁻¹ = b := by
      have := hnA b hb
      calc n * b * n⁻¹ = n * (n⁻¹ * b * n) * n⁻¹ := by rw [this]
        _ = b := by group
    calc m⁻¹ * b * m = w⁻¹ * (n * b * n⁻¹) * w := by rw [hm]; group
      _ = b := by rw [h2, h1]
  have hcD : m * d * m⁻¹ * d⁻¹ ∈ D := mul_mem (hnD d hdD) (inv_mem hdD)
  have hcV : m * d * m⁻¹ * d⁻¹ ∈ normalizer (V : Set G) := hDV hcD
  have hcodd : Odd (orderOf (m * d * m⁻¹ * d⁻¹)) :=
    Odd.of_dvd_nat hDodd (Subgroup.orderOf_dvd_natCard D hcD)
  have hcA : ∀ x ∈ V, x ^ 2 = 1 →
      (m * d * m⁻¹ * d⁻¹) * x * (m * d * m⁻¹ * d⁻¹)⁻¹ = x := by
    intro x hx hx2
    have hb := hΩ x hx hx2
    have hy : d⁻¹ * x * d ∈ szA₁ (szT₁ L T) := (mem_normalizer_iff''.mp hdA x).mp hb
    have hmx : m * x * m⁻¹ = x := by
      have := hmA x hb
      calc m * x * m⁻¹ = m * (m⁻¹ * x * m) * m⁻¹ := by rw [this]
        _ = x := by group
    calc (m * d * m⁻¹ * d⁻¹) * x * (m * d * m⁻¹ * d⁻¹)⁻¹ =
        m * d * (m⁻¹ * (d⁻¹ * x * d) * m) * d⁻¹ * m⁻¹ := by group
      _ = m * x * m⁻¹ := by rw [hmA _ hy]; group
      _ = x := hmx
  have hcVc := pushUp_conj_eq_of_odd hVc hpow hcV hcodd (pow_orderOf_eq_one _) hcA
  have hnV : ∀ y ∈ V, n * y * n⁻¹ = y := fun y hy => by
    rw [mul_inv_eq_iff_eq_mul]; exact mem_centralizer_iff.mp (hVT₁ hy) n hn
  have hw : w = n * m := by rw [hm, mul_inv_cancel_left]
  have hwd : ∀ x ∈ V, w * (d * x * d⁻¹) * w⁻¹ = d * (w * x * w⁻¹) * d⁻¹ := by
    intro x hx
    have hdx : d * x * d⁻¹ ∈ V := (mem_normalizer_iff.mp hdV x).mp hx
    have hmx : m * x * m⁻¹ ∈ V := (mem_normalizer_iff.mp hmV x).mp hx
    have hmdx : m * (d * x * d⁻¹) * m⁻¹ ∈ V := (mem_normalizer_iff.mp hmV _).mp hdx
    have hdmx : d * (m * x * m⁻¹) * d⁻¹ ∈ V := (mem_normalizer_iff.mp hdV _).mp hmx
    have hkey := hcVc _ hdmx
    rw [show (m * d * m⁻¹ * d⁻¹) * (d * (m * x * m⁻¹) * d⁻¹) * (m * d * m⁻¹ * d⁻¹)⁻¹ =
      m * (d * x * d⁻¹) * m⁻¹ by group] at hkey
    calc w * (d * x * d⁻¹) * w⁻¹ = n * (m * (d * x * d⁻¹) * m⁻¹) * n⁻¹ := by rw [hw]; group
      _ = m * (d * x * d⁻¹) * m⁻¹ := hnV _ hmdx
      _ = d * (m * x * m⁻¹) * d⁻¹ := hkey
      _ = d * (n * (m * x * m⁻¹) * n⁻¹) * d⁻¹ := by rw [hnV _ hmx]
      _ = d * (w * x * w⁻¹) * d⁻¹ := by rw [hw]; group
  exact pushUp_sign_dichotomy hVc (pow_pos (by norm_num) f) he hcard hpow hΩ (le_of_eq hA₁card)
    hdV htr hwV hw2 hwA' hwd

end U3Start

end CFSG.SeitzReduction.RankOne
