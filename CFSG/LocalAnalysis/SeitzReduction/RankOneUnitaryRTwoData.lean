module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiCoordsBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

structure U3R2 (G : Type) [Group G] [Finite G] (L T₁ R₂ : Subgroup G) (t : G) (f : ℕ) : Prop where
  comm : ∀ x ∈ R₂, ∀ y ∈ R₂, x * y = y * x
  card : Nat.card R₂ = (2 ^ f) ^ 2
  le : szA₁ T₁ ≤ R₂
  inf : T₁ ⊓ R₂ = szA₁ T₁
  commT₁ : ∀ x ∈ T₁, ∀ r ∈ R₂, x * r = r * x
  tN : ∀ r ∈ R₂, t * r * t⁻¹ ∈ R₂
  rho_onto : ∀ b ∈ szA₁ T₁, ∃ r ∈ R₂, r * t * r⁻¹ * t = b
  rho_ker : ∀ r ∈ R₂, r * t = t * r → r ∈ szA₁ T₁
  t_sq : t ^ 2 = 1
  t_comm : ∀ x ∈ T₁, x * t = t * x
  sq_A₁ : ∀ b ∈ szA₁ T₁, b ^ 2 = 1
  sq_mem : ∀ r ∈ R₂, r ^ 2 ∈ szA₁ T₁
  rho_mem : ∀ r ∈ R₂, r * t * r⁻¹ * t ∈ szA₁ T₁
  torus : ∃ d : G, d * t = t * d ∧ d ∈ normalizer (R₂ : Set G) ∧ d ∈ normalizer (T₁ : Set G) ∧
    ∀ b ∈ szA₁ T₁, ∀ b' ∈ szA₁ T₁, b ≠ 1 → b' ≠ 1 → ∃ n : ℕ, (d ^ n)⁻¹ * b * d ^ n = b'

namespace U3R2

variable {G : Type} [Group G] [Finite G] {L T₁ R₂ : Subgroup G} {t : G} {f : ℕ}
  (hR : U3R2 G L T₁ R₂ t f)
include hR

theorem t_inv : t⁻¹ = t := by
  rw [inv_eq_iff_mul_eq_one, ← sq, hR.t_sq]

theorem szA₁_comm_t {b : G} (hb : b ∈ szA₁ T₁) : b * t = t * b := hR.t_comm b (szA₁_le T₁ hb)

theorem conj_t_eq (u : G) : u * t * u⁻¹ = (u * t * u⁻¹ * t) * t := by
  rw [mul_assoc (u * t * u⁻¹) t t, ← sq, hR.t_sq, mul_one]

omit hR [Finite G] in
theorem rho_conj {D u : G} (hD : D * t = t * D) :
    D⁻¹ * u * D * t * (D⁻¹ * u * D)⁻¹ * t = D⁻¹ * (u * t * u⁻¹ * t) * D := by
  have hDt : D * t * D⁻¹ = t := by rw [hD, mul_inv_cancel_right]
  calc D⁻¹ * u * D * t * (D⁻¹ * u * D)⁻¹ * t =
      D⁻¹ * u * (D * t * D⁻¹) * u⁻¹ * (D * t * D⁻¹) * D := by group
    _ = D⁻¹ * (u * t * u⁻¹ * t) * D := by rw [hDt]; group

theorem sq_eq_of_rho_eq {u v : G} (hu : u ∈ R₂) (hv : v ∈ R₂)
    (huv : u * t * u⁻¹ * t = v * t * v⁻¹ * t) : u ^ 2 = v ^ 2 := by
  have h1 : u * t * u⁻¹ = v * t * v⁻¹ := by rw [hR.conj_t_eq u, hR.conj_t_eq v, huv]
  have ha : u⁻¹ * v ∈ szA₁ T₁ := by
    refine hR.rho_ker _ (mul_mem (inv_mem hu) hv) ?_
    calc u⁻¹ * v * t = u⁻¹ * (v * t * v⁻¹) * v := by group
      _ = u⁻¹ * (u * t * u⁻¹) * v := by rw [h1]
      _ = t * (u⁻¹ * v) := by group
  have hua : Commute u (u⁻¹ * v) := hR.comm u hu _ (hR.le ha)
  have hv' : v = u * (u⁻¹ * v) := by group
  rw [hv', hua.mul_pow, hR.sq_A₁ _ ha, mul_one]

theorem rho_ne_one {u : G} (hu : u ∈ R₂) (huA : u ∉ szA₁ T₁) : u * t * u⁻¹ * t ≠ 1 := by
  intro h1
  apply huA
  refine hR.rho_ker u hu ?_
  have h2 : u * t * u⁻¹ = t := by
    have := hR.conj_t_eq u
    rwa [h1, one_mul] at this
  calc u * t = u * t * u⁻¹ * u := by group
    _ = t * u := by rw [h2]

theorem sq_eq_conj_of_not_mem {d : G} (hdt : d * t = t * d) (hdR : d ∈ normalizer (R₂ : Set G))
    (htr : ∀ b ∈ szA₁ T₁, ∀ b' ∈ szA₁ T₁, b ≠ 1 → b' ≠ 1 → ∃ n : ℕ, (d ^ n)⁻¹ * b * d ^ n = b')
    {u₀ u : G} (hu₀ : u₀ ∈ R₂) (hu₀A : u₀ ∉ szA₁ T₁) (hu : u ∈ R₂) (huA : u ∉ szA₁ T₁) :
    ∃ n : ℕ, u ^ 2 = (d ^ n)⁻¹ * u₀ ^ 2 * d ^ n ∧
      u * t * u⁻¹ * t = (d ^ n)⁻¹ * (u₀ * t * u₀⁻¹ * t) * d ^ n := by
  obtain ⟨n, hn⟩ := htr _ (hR.rho_mem u₀ hu₀) _ (hR.rho_mem u hu) (hR.rho_ne_one hu₀ hu₀A)
    (hR.rho_ne_one hu huA)
  have hDt : d ^ n * t = t * d ^ n := (Commute.pow_left hdt n).eq
  have hvR : (d ^ n)⁻¹ * u₀ * d ^ n ∈ R₂ := by
    have := (mem_normalizer_iff.mp (inv_mem (pow_mem hdR n)) u₀).mp hu₀
    rwa [inv_inv] at this
  refine ⟨n, ?_, hn.symm⟩
  rw [hR.sq_eq_of_rho_eq hu hvR (by rw [rho_conj hDt, hn]), sq, sq]
  group

theorem sq_eq_one_or : (∀ r ∈ R₂, r ^ 2 = 1) ∨ ∀ r ∈ R₂, r ^ 2 = 1 → r ∈ szA₁ T₁ := by
  by_cases hall : ∀ r ∈ R₂, r ^ 2 = 1
  · exact Or.inl hall
  push Not at hall
  obtain ⟨u₀, hu₀, hu₀2⟩ := hall
  have hu₀A : u₀ ∉ szA₁ T₁ := fun h => hu₀2 (hR.sq_A₁ u₀ h)
  obtain ⟨d, hdt, hdR, -, htr⟩ := hR.torus
  refine Or.inr fun r hr hr2 => ?_
  by_contra hrA
  obtain ⟨n, hn, -⟩ := hR.sq_eq_conj_of_not_mem hdt hdR htr hu₀ hu₀A hr hrA
  apply hu₀2
  have h1 : (d ^ n)⁻¹ * u₀ ^ 2 * d ^ n = 1 := by rw [← hn, hr2]
  calc u₀ ^ 2 = d ^ n * ((d ^ n)⁻¹ * u₀ ^ 2 * d ^ n) * (d ^ n)⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem sq_mul_t {r : G} (hr : r ∈ R₂) : (r * t) ^ 2 = (r * t * r⁻¹ * t) * r ^ 2 := by
  have h1 : r ^ 2 * t = t * r ^ 2 := hR.szA₁_comm_t (hR.sq_mem r hr)
  calc (r * t) ^ 2 = r * t * r⁻¹ * (r ^ 2 * t) := by rw [sq, sq]; group
    _ = (r * t * r⁻¹ * t) * r ^ 2 := by rw [h1]; group

omit hR [Finite G] in
theorem sq_mul_eq_one_iff (ht : t ^ 2 = 1) {r : G} : (r * t) ^ 2 = 1 ↔ t * r * t⁻¹ = r⁻¹ := by
  have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← sq, ht]
  rw [htinv, sq]
  constructor
  · intro h1
    calc t * r * t = r⁻¹ * (r * t * (r * t)) := by group
      _ = r⁻¹ := by rw [h1, mul_one]
  · intro h1
    calc r * t * (r * t) = r * (t * r * t) := by group
      _ = 1 := by rw [h1, mul_inv_cancel]

theorem mem_szA_of_sq_eq_one (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) {r : G} (hr : r ∈ R₂)
    (h2 : (r * t) ^ 2 = 1) : r ∈ szA₁ T₁ := by
  by_contra hrA
  apply hc
  obtain ⟨d, hdt, hdR, -, htr⟩ := hR.torus
  have hρ2 := hR.sq_A₁ _ (hR.rho_mem r hr)
  have h3 := hR.sq_mul_t hr
  rw [h2] at h3
  have hr2 : r ^ 2 = r * t * r⁻¹ * t := by
    calc r ^ 2 = (r * t * r⁻¹ * t) ^ 2 * r ^ 2 := by rw [hρ2, one_mul]
      _ = (r * t * r⁻¹ * t) * ((r * t * r⁻¹ * t) * r ^ 2) := by rw [sq]; group
      _ = r * t * r⁻¹ * t := by rw [← h3, mul_one]
  intro u hu
  rw [← sq_mul_eq_one_iff hR.t_sq]
  by_cases huA : u ∈ szA₁ T₁
  · rw [hR.sq_mul_t hu, hR.sq_A₁ u huA, mul_one, hR.szA₁_comm_t huA, mul_inv_cancel_right, ← sq,
      hR.t_sq]
  · obtain ⟨n, hn, hρn⟩ := hR.sq_eq_conj_of_not_mem hdt hdR htr hr hrA hu huA
    have hu2 : u ^ 2 = u * t * u⁻¹ * t := by rw [hn, hr2, hρn]
    rw [hR.sq_mul_t hu, hu2, ← sq, hR.sq_A₁ _ (hR.rho_mem u hu)]

end U3R2

end CFSG.SeitzReduction.RankOne
