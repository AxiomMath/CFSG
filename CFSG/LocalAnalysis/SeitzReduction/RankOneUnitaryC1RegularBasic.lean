module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1UOne

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1Regular

theorem mem_normalizer_centralizer_of_mem_normalizer {G : Type*} [Group G] {H : Subgroup G}
    {y : G} (hy : y ∈ normalizer (H : Set G)) :
    y ∈ normalizer (centralizer (H : Set G) : Set G) := by
  have key : ∀ z ∈ normalizer (H : Set G), ∀ c ∈ centralizer (H : Set G),
      z * c * z⁻¹ ∈ centralizer (H : Set G) := by
    intro z hz c hc
    refine mem_centralizer_iff.mpr fun x hx => ?_
    have hx' : z⁻¹ * x * z ∈ H := (mem_normalizer_iff''.mp hz x).mp hx
    have h1 := mem_centralizer_iff.mp hc _ hx'
    calc x * (z * c * z⁻¹) = z * ((z⁻¹ * x * z) * c) * z⁻¹ := by group
      _ = z * (c * (z⁻¹ * x * z)) * z⁻¹ := by rw [h1]
      _ = z * c * z⁻¹ * x := by group
  refine mem_normalizer_iff.mpr fun c => ⟨key y hy c, fun hc => ?_⟩
  have := key y⁻¹ (inv_mem hy) _ hc
  rwa [show y⁻¹ * (y * c * y⁻¹) * y⁻¹⁻¹ = c by group] at this

theorem mem_normalizer_inf_of_mem {G : Type*} [Group G] {H K : Subgroup G} {y : G}
    (hH : y ∈ normalizer (H : Set G)) (hK : y ∈ normalizer (K : Set G)) :
    y ∈ normalizer ((H ⊓ K : Subgroup G) : Set G) :=
  mem_normalizer_iff.mpr fun c =>
    ⟨fun hc => mem_inf.mpr ⟨(mem_normalizer_iff.mp hH c).mp (mem_inf.mp hc).1,
        (mem_normalizer_iff.mp hK c).mp (mem_inf.mp hc).2⟩,
      fun hc => mem_inf.mpr ⟨(mem_normalizer_iff.mp hH c).mpr (mem_inf.mp hc).1,
        (mem_normalizer_iff.mp hK c).mpr (mem_inf.mp hc).2⟩⟩

end U3C1Regular

namespace U3R2

variable {G : Type} [Group G] [Finite G] {L T₁ R₂ : Subgroup G} {t : G} {f : ℕ}

theorem szR_le_centralizer_szA₁ (hR : U3R2 G L T₁ R₂ t f) :
    szR T₁ R₂ t ≤ centralizer (szA₁ T₁ : Set G) := by
  refine sup_le (sup_le (fun y hy => ?_) (fun r hr => ?_)) (zpowers_le.mpr ?_)
  · exact mem_centralizer_iff.mpr fun b hb =>
      (mem_centralizer_iff.mp (mem_szA₁.mp hb).2 y hy).symm
  · exact mem_centralizer_iff.mpr fun b hb => hR.comm b (hR.le hb) r hr
  · exact mem_centralizer_iff.mpr fun b hb => hR.t_comm b (szA₁_le _ hb)

theorem exists_inv_mul_conj_pow_mem (hR : U3R2 G L T₁ R₂ t f)
    (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) {d : G} (hdR : d ∈ normalizer (R₂ : Set G))
    (htr : ∀ b ∈ szA₁ T₁, ∀ b' ∈ szA₁ T₁, b ≠ 1 → b' ≠ 1 → ∃ n : ℕ, (d ^ n)⁻¹ * b * d ^ n = b')
    {r₀ r : G} (hr₀ : r₀ ∈ R₂) (hr₀A : r₀ ∉ szA₁ T₁) (hr : r ∈ R₂) (hrA : r ∉ szA₁ T₁) :
    ∃ n : ℕ, r⁻¹ * ((d ^ n)⁻¹ * r₀ * d ^ n) ∈ szA₁ T₁ := by
  have h0 : r₀ ^ 2 ≠ 1 := fun h1 => hr₀A (hR.mem_szA₁_of_sq_eq_one_of_inv hinv hr₀ h1)
  have h1 : r ^ 2 ≠ 1 := fun h1 => hrA (hR.mem_szA₁_of_sq_eq_one_of_inv hinv hr h1)
  obtain ⟨n, hn⟩ := htr _ (hR.sq_mem r₀ hr₀) _ (hR.sq_mem r hr) h0 h1
  refine ⟨n, ?_⟩
  have hs : (d ^ n)⁻¹ * r₀ * d ^ n ∈ R₂ := by
    have := (mem_normalizer_iff''.mp (pow_mem hdR n) r₀).mp hr₀
    simpa using this
  refine hR.mem_szA₁_of_sq_eq_one_of_inv hinv (mul_mem (inv_mem hr) hs) ?_
  have hc : Commute r⁻¹ ((d ^ n)⁻¹ * r₀ * d ^ n) := hR.comm _ (inv_mem hr) _ hs
  rw [hc.mul_pow, show ((d ^ n)⁻¹ * r₀ * d ^ n) ^ 2 = (d ^ n)⁻¹ * r₀ ^ 2 * d ^ n by
    rw [sq, sq]; group, hn, inv_pow, inv_mul_cancel]

end U3R2

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_regular_of_transitive (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hne : ∃ r ∈ R₂, r ^ 2 ≠ 1)
    (htr : ∀ r ∈ R₂, ∃ x ∈ normalizer (szR (szT₁ L T) R₂ t : Set G) ⊓
      centralizer (szA₁ (szT₁ L T) : Set G), x * t * x⁻¹ * (r * t)⁻¹ ∈ szA₁ (szT₁ L T)) :
    ∃ E : Subgroup G, E ≤ normalizer (szR (szT₁ L T) R₂ t : Set G) ∧
      normalizer (szR (szT₁ L T) R₂ t : Set G) ≤ normalizer (E : Set G) ∧
      szR (szT₁ L T) R₂ t ≤ E ∧ E ≤ centralizer (szA₁ (szT₁ L T) : Set G) ∧
      (∀ x ∈ E, x * t * x⁻¹ ∈ szA L T t → ∀ r ∈ R₂,
        x * (r * t) * x⁻¹ * (r * t)⁻¹ ∈ szA₁ (szT₁ L T)) ∧
      ∀ r ∈ R₂, ∃ x ∈ E, x * t * x⁻¹ * (r * t)⁻¹ ∈ szA₁ (szT₁ L T) := by
  obtain ⟨-, hYA⟩ := h.normalizer_szR_le_normalizer_szT₁_of_inv hS2 hR hinv hne
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  refine ⟨normalizer (szR (szT₁ L T) R₂ t : Set G) ⊓ centralizer (szA₁ (szT₁ L T) : Set G),
    inf_le_left, fun y hy => U3C1Regular.mem_normalizer_inf_of_mem (Subgroup.le_normalizer hy)
      (U3C1Regular.mem_normalizer_centralizer_of_mem_normalizer (hYA hy)),
    le_inf Subgroup.le_normalizer hR.szR_le_centralizer_szA₁, inf_le_right, ?_, htr⟩
  rintro x ⟨hxY, hxC⟩ hxt r hr
  have ha := h.exists_conj_t_eq_of_mem_szA hS2 hR hinv hxY hxt
  have hb := hR.conj_mem_of_inv hinv (mem_inf.mp (hNR₁ hxY)).2
    (fun b hb => by rw [← mem_centralizer_iff.mp hxC b hb, mul_inv_cancel_right]) hr
  set a := x * t * x⁻¹ * t⁻¹ with hadef
  set b := r⁻¹ * (x * r * x⁻¹) with hbdef
  have hab : b * a ∈ R₂ := hR.le (mul_mem hb ha)
  have e : x * (r * t) * x⁻¹ * (r * t)⁻¹ = r * (b * a) * r⁻¹ := by
    rw [hadef, hbdef]; group
  rw [e, hR.comm r hr _ hab, mul_inv_cancel_right]
  exact mul_mem hb ha

theorem exists_conj_t_of_move {R₂ : Subgroup G} (hR : U3R2 G L (szT₁ L T) R₂ t f)
    (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) {Y : Subgroup G} {y₀ r₀ : G} (hy₀ : y₀ ∈ Y)
    (hr₀ : r₀ ∈ R₂) (hr₀A : r₀ ∉ szA₁ (szT₁ L T)) (hy₀t : y₀ * t * y₀⁻¹ = r₀ * t) {d : G}
    (hdY : d ∈ Y) (hdt : d * t = t * d) (hdR : d ∈ normalizer (R₂ : Set G))
    (hdtr : ∀ b ∈ szA₁ (szT₁ L T), ∀ b' ∈ szA₁ (szT₁ L T), b ≠ 1 → b' ≠ 1 →
      ∃ n : ℕ, (d ^ n)⁻¹ * b * d ^ n = b') :
    ∀ r ∈ R₂, ∃ y ∈ Y, y * t * y⁻¹ * (r * t)⁻¹ ∈ szA₁ (szT₁ L T) := by
  intro r hr
  by_cases hrA : r ∈ szA₁ (szT₁ L T)
  · refine ⟨1, one_mem _, ?_⟩
    rw [show (1 : G) * t * 1⁻¹ * (r * t)⁻¹ = r⁻¹ by group]
    exact inv_mem hrA
  obtain ⟨n, hn⟩ := hR.exists_inv_mul_conj_pow_mem hinv hdR hdtr hr₀ hr₀A hr hrA
  refine ⟨(d ^ n)⁻¹ * y₀, mul_mem (inv_mem (pow_mem hdY n)) hy₀, ?_⟩
  have hdnt : d ^ n * t = t * d ^ n := (Commute.pow_left hdt n).eq
  have hs : (d ^ n)⁻¹ * r₀ * d ^ n ∈ R₂ := by
    have := (mem_normalizer_iff''.mp (pow_mem hdR n) r₀).mp hr₀
    simpa using this
  have e : (d ^ n)⁻¹ * y₀ * t * ((d ^ n)⁻¹ * y₀)⁻¹ * (r * t)⁻¹ =
      ((d ^ n)⁻¹ * r₀ * d ^ n) * r⁻¹ := by
    have e1 : (d ^ n)⁻¹ * y₀ * t * ((d ^ n)⁻¹ * y₀)⁻¹ =
        (d ^ n)⁻¹ * (y₀ * t * y₀⁻¹) * d ^ n := by group
    have e2 : t * d ^ n = d ^ n * t := hdnt.symm
    rw [e1, hy₀t]
    calc (d ^ n)⁻¹ * (r₀ * t) * d ^ n * (r * t)⁻¹ = (d ^ n)⁻¹ * r₀ * (t * d ^ n) * t⁻¹ * r⁻¹ := by
          group
      _ = (d ^ n)⁻¹ * r₀ * d ^ n * r⁻¹ := by rw [e2]; group
  have hc : Commute r ((d ^ n)⁻¹ * r₀ * d ^ n) := hR.comm _ hr _ hs
  rw [e, ← hc.inv_left.eq]
  exact hn

end U3Start

end CFSG.SeitzReduction.RankOne
