module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterStepLevel

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

namespace U3C1OuterLevelData

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G}

section Facts

variable (hS : U3C1OuterStepHyp G L f t T R₂ D d V 1)
  (hL : U3C1OuterLevelData G L f t T D V U U₁ 1)
include hS hL

theorem muOne_t_mul_self : t * t = 1 := by rw [← sq, hS.start.sq_eq_one]

theorem muOne_comm_t_mem {x : G} (hx : x ∈ U) : x * t * x⁻¹ * t⁻¹ ∈ V :=
  hL.comm_t_mem hS.start hS.card_sylow hS.conf hx

theorem muOne_conj_V {x : G} (hx : x ∈ U₁) {r : G} (hr : r ∈ V) : x * r * x⁻¹ ∈ V := by
  have h1 := hL.conj_V₁ x hx r hr
  rw [show x * r * x⁻¹ = r * (r⁻¹ * (x * r * x⁻¹)) by group]
  exact mul_mem hr (hS.conf.le h1)

theorem muOne_sq_mem_szA₁_of_mem_V {r : G} (hr : r ∈ V) : r ^ 2 ∈ szA₁ (szT₁ L T) := by
  refine hS.conf.omega _ (pow_mem hr 2) ?_
  calc (r ^ 2) ^ 2 = r ^ 2 ^ (1 + 1) := by rw [← pow_mul]; norm_num
    _ = 1 := hS.conf.pow r hr

theorem muOne_conj_szA₁ {x : G} (hx : x ∈ U₁) {b : G} (hb : b ∈ szA₁ (szT₁ L T)) :
    x * b * x⁻¹ = b :=
  hL.conj_szA₁ x (hL.U₁_le hx) b hb

theorem muOne_T₁_comm {y : G} (hy : y ∈ szT₁ L T) {r : G} (hr : r ∈ V) : y * r = r * y :=
  mem_centralizer_iff.mp (hS.conf.le_centralizer hr) y hy

theorem muOne_T₁_le_normalizer : szT₁ L T ≤ normalizer (V : Set G) := fun y hy =>
  mem_normalizer_of_forall_inv_mul_mul_mem fun r hr => by
    rw [show y⁻¹ * r * y = r by rw [mul_assoc, ← hL.muOne_T₁_comm hS hy hr, inv_mul_cancel_left]]
    exact hr

theorem muOne_sup_le_centralizer : szT₁ L T ⊔ V ≤ centralizer (V : Set G) :=
  sup_le (fun _ hy => mem_centralizer_iff.mpr fun _ hr => (hL.muOne_T₁_comm hS hy hr).symm)
    (fun r hr => mem_centralizer_iff.mpr fun r' hr' => hS.conf.comm r' hr' r hr)

theorem muOne_comm_t_of_mem_sup {y r : G} (hy : y ∈ szT₁ L T) (hr : r ∈ V) :
    y * r * t * (y * r)⁻¹ * t⁻¹ = r ^ 2 := by
  have hyt : y * t = t * y := mem_centralizer_iff.mp hS.start.mem_centralizer_szT₁ y hy
  have hσr : r * t * r⁻¹ * t⁻¹ = r ^ 2 := SzC1.comm_eq_sq_of_inv (hS.conf.inv r hr)
  have hyr2 : y * r ^ 2 * y⁻¹ = r ^ 2 := by
    rw [show y * r ^ 2 = r ^ 2 * y from hL.muOne_T₁_comm hS hy (pow_mem hr 2),
      mul_inv_cancel_right]
  rw [SzC1.comm_t_mul, hσr, hyr2, show y * t * y⁻¹ * t⁻¹ = 1 by rw [hyt]; group, mul_one]

theorem muOne_sq_mul_mul_t {y r : G} (hy : y ∈ szT₁ L T) (hr : r ∈ V) :
    (y * r * t) ^ 2 = y ^ 2 := by
  have e1 : t * y = y * t := (mem_centralizer_iff.mp hS.start.mem_centralizer_szT₁ y hy).symm
  have e3 : r * y = y * r := (hL.muOne_T₁_comm hS hy hr).symm
  have htr : t * r = r⁻¹ * t := by
    have := hS.conf.inv r hr
    calc t * r = t * r * t⁻¹ * t := by group
      _ = r⁻¹ * t := by rw [this]
  calc (y * r * t) ^ 2 = y * r * (t * y) * r * t := by rw [sq]; group
    _ = y * (r * y) * (t * r) * t := by rw [e1]; group
    _ = y * (y * r) * (r⁻¹ * t) * t := by rw [e3, htr]
    _ = y * y * (t * t) := by group
    _ = y ^ 2 := by rw [hL.muOne_t_mul_self hS, mul_one, sq]

theorem muOne_comm_t_mem_szA₁_of_mem_sup {x : G} (hx : x ∈ szT₁ L T ⊔ V) :
    x * t * x⁻¹ * t⁻¹ ∈ szA₁ (szT₁ L T) := by
  obtain ⟨y, hy, r, hr, rfl⟩ := ncyc_exists_mul_of_mem_sup (hL.muOne_T₁_le_normalizer hS) hx
  have hyt : y * t = t * y := mem_centralizer_iff.mp hS.start.mem_centralizer_szT₁ y hy
  have hσr : r * t * r⁻¹ * t⁻¹ = r ^ 2 := SzC1.comm_eq_sq_of_inv (hS.conf.inv r hr)
  have hr2 := hL.muOne_sq_mem_szA₁_of_mem_V hS hr
  have hyr2 : y * r ^ 2 * y⁻¹ = r ^ 2 := by
    rw [show y * r ^ 2 = r ^ 2 * y from hL.muOne_T₁_comm hS hy (pow_mem hr 2),
      mul_inv_cancel_right]
  have e : y * r * t * (y * r)⁻¹ * t⁻¹ = r ^ 2 := by
    rw [SzC1.comm_t_mul, hσr, hyr2, show y * t * y⁻¹ * t⁻¹ = 1 by rw [hyt]; group, mul_one]
  rw [e]
  exact hr2

theorem muOne_mem_sup_of_comm_t_mem_szA₁ {x : G} (hx : x ∈ U₁)
    (hσ : x * t * x⁻¹ * t⁻¹ ∈ szA₁ (szT₁ L T)) : x ∈ szT₁ L T ⊔ V := by
  have hR : x ∈ szR (szT₁ L T) V t := by
    by_contra hR
    refine hL.conj_t_not_mem x (hL.U₁_le hx) hR ?_
    rw [show x * t * x⁻¹ = (x * t * x⁻¹ * t⁻¹) * t by group]
    exact mul_mem (szA₁_le_szA L T t hσ) (mem_szA_right L T t)
  rw [← hL.inf_eq]
  exact mem_inf.mpr ⟨hx, hR⟩

theorem muOne_comm_t_conj_d (y : G) :
    d⁻¹ * y * d * t * (d⁻¹ * y * d)⁻¹ * t⁻¹ = d⁻¹ * (y * t * y⁻¹ * t⁻¹) * d := by
  have hdt : d * t = t * d := mem_centralizer_iff.mp hS.start.mem d (hS.cartan.le hS.cartan.mem)
  have e1 : d * t * d⁻¹ = t := by rw [hdt, mul_inv_cancel_right]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (hL.muOne_t_mul_self hS)
  have e2 : d * t⁻¹ * d⁻¹ = t⁻¹ := by rw [htinv, e1]
  calc d⁻¹ * y * d * t * (d⁻¹ * y * d)⁻¹ * t⁻¹ =
        d⁻¹ * (y * (d * t * d⁻¹) * y⁻¹ * (d * t⁻¹ * d⁻¹)) * d := by group
    _ = _ := by rw [e1, e2]

theorem muOne_conj_d_mem_U₁ {x : G} (hx : x ∈ U₁) : d⁻¹ * x * d ∈ U₁ := by
  simpa using (mem_normalizer_iff.mp (inv_mem (hL.D_le hS.cartan.mem)) x).mp hx

end Facts

section Coords

variable (hS : U3C1OuterStepHyp G L f t T R₂ D d V 1)
  (hL : U3C1OuterLevelData G L f t T D V U U₁ 1) {K : Type} [Field K] [Fintype K] [CharP K 2]
  {v : G → K} {μ : K} (hc : U3A₁Coords (szA₁ (szT₁ L T)) d v μ)
include hS hL hc

theorem muOne_S_mul {x y : G} (hx : x ∈ U₁) (hy : y ∈ U₁) :
    v ((x * y * t * (x * y)⁻¹ * t⁻¹) ^ 2) =
      v ((x * t * x⁻¹ * t⁻¹) ^ 2) + v ((y * t * y⁻¹ * t⁻¹) ^ 2) := by
  have hσy := hL.muOne_comm_t_mem hS (hL.U₁_le hy)
  have hσx := hL.muOne_comm_t_mem hS (hL.U₁_le hx)
  rw [SzC1.comm_t_mul, (Commute.mul_pow (hS.conf.comm _ (hL.muOne_conj_V hS hx hσy) _ hσx) _),
    conj_pow, hL.muOne_conj_szA₁ hS hx (hL.muOne_sq_mem_szA₁_of_mem_V hS hσy),
    hc.mul _ (hL.muOne_sq_mem_szA₁_of_mem_V hS hσy) _ (hL.muOne_sq_mem_szA₁_of_mem_V hS hσx),
    add_comm]

theorem muOne_S_conj_d {x : G} (hx : x ∈ U₁) :
    v ((d⁻¹ * x * d * t * (d⁻¹ * x * d)⁻¹ * t⁻¹) ^ 2) = μ * v ((x * t * x⁻¹ * t⁻¹) ^ 2) := by
  have e : (d⁻¹ * (x * t * x⁻¹ * t⁻¹) * d) ^ 2 = d⁻¹ * (x * t * x⁻¹ * t⁻¹) ^ 2 * d := by
    simpa only [inv_inv] using conj_pow (a := d⁻¹) (b := x * t * x⁻¹ * t⁻¹) (i := 2)
  rw [hL.muOne_comm_t_conj_d hS x, e,
    hc.conj _ (hL.muOne_sq_mem_szA₁_of_mem_V hS (hL.muOne_comm_t_mem hS (hL.U₁_le hx)))]

theorem muOne_mem_sup_of_S_eq_zero {x : G} (hx : x ∈ U₁) (h0 : v ((x * t * x⁻¹ * t⁻¹) ^ 2) = 0) :
    x ∈ szT₁ L T ⊔ V := by
  have hσ := hL.muOne_comm_t_mem hS (hL.U₁_le hx)
  have h1 : (x * t * x⁻¹ * t⁻¹) ^ 2 = 1 :=
    hc.eq_one_of_v_eq_zero (hL.muOne_sq_mem_szA₁_of_mem_V hS hσ) h0
  exact hL.muOne_mem_sup_of_comm_t_mem_szA₁ hS hx (hS.conf.omega _ hσ h1)

theorem muOne_exists_S_ne_zero (hμV : ¬ U₁ ≤ centralizer (V : Set G)) :
    ∃ x ∈ U₁, v ((x * t * x⁻¹ * t⁻¹) ^ 2) ≠ 0 := by
  by_contra hne
  push Not at hne
  exact hμV fun x hx =>
    hL.muOne_sup_le_centralizer hS (hL.muOne_mem_sup_of_S_eq_zero hS hc hx (hne x hx))

theorem muOne_S_surj (hμV : ¬ U₁ ≤ centralizer (V : Set G))
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) (s : K) :
    ∃ x ∈ U₁, v ((x * t * x⁻¹ * t⁻¹) ^ 2) = s := by
  by_cases hs : s = 0
  · exact ⟨1, one_mem _, by simp [hs, hc.v_one]⟩
  obtain ⟨x₀, hx₀, hS₀⟩ := hL.muOne_exists_S_ne_zero hS hc hμV
  obtain ⟨m, hm⟩ := hμ (s / v ((x₀ * t * x₀⁻¹ * t⁻¹) ^ 2)) (div_ne_zero hs hS₀)
  have key : ∀ n : ℕ, ∃ x ∈ U₁, v ((x * t * x⁻¹ * t⁻¹) ^ 2) =
      μ ^ n * v ((x₀ * t * x₀⁻¹ * t⁻¹) ^ 2) := by
    intro n
    induction n with
    | zero => exact ⟨x₀, hx₀, by rw [pow_zero, one_mul]⟩
    | succ n ih =>
      obtain ⟨x, hx, hxS⟩ := ih
      refine ⟨d⁻¹ * x * d, hL.muOne_conj_d_mem_U₁ hS hx, ?_⟩
      rw [hL.muOne_S_conj_d hS hc hx, hxS, pow_succ]
      ring
  obtain ⟨x, hx, hxS⟩ := key m
  exact ⟨x, hx, by rw [hxS, hm, div_mul_cancel₀ s hS₀]⟩

theorem muOne_exists_comm_t_eq (hμV : ¬ U₁ ≤ centralizer (V : Set G))
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) {r : G} (hr : r ∈ V) :
    ∃ y ∈ U₁, y * t * y⁻¹ * t⁻¹ = r := by
  obtain ⟨-, hA₁card, -⟩ := hS.start.facts_of_card_sylow hS.card_sylow
  obtain ⟨y₀, hy₀, hSy⟩ := hL.muOne_S_surj hS hc hμV hμ (v (r ^ 2))
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀, σ₀ = y₀ * t * y₀⁻¹ * t⁻¹ := ⟨_, rfl⟩
  have hσ : σ₀ ∈ V := hσ₀ ▸ hL.muOne_comm_t_mem hS (hL.U₁_le hy₀)
  rw [← hσ₀] at hSy
  have heq : σ₀ ^ 2 = r ^ 2 :=
    hc.inj _ (hL.muOne_sq_mem_szA₁_of_mem_V hS hσ) _ (hL.muOne_sq_mem_szA₁_of_mem_V hS hr) hSy
  have h1 : (σ₀⁻¹ * r) ^ 2 ^ 1 = 1 := by
    rw [pow_one, (Commute.mul_pow (hS.conf.comm _ (inv_mem hσ) _ hr) _), inv_pow, heq,
      inv_mul_cancel]
  obtain ⟨w, hw, hw2⟩ := SzC1.exists_sq_eq_of_pow_eq_one (k := 1) hS.conf.comm hS.conf.omega
    hS.conf.pow (by rw [hA₁card, hS.conf.card]) (mul_mem (inv_mem hσ) hr) h1
  have hwU₁ : w ∈ U₁ := hL.sup_le_U₁ (mem_sup_right hw)
  refine ⟨w * y₀, mul_mem hwU₁ hy₀, ?_⟩
  have hc1 : w * σ₀ * w⁻¹ = σ₀ := by rw [hS.conf.comm w hw σ₀ hσ, mul_inv_cancel_right]
  rw [SzC1.comm_t_mul, ← hσ₀, SzC1.comm_eq_sq_of_inv (hS.conf.inv w hw), hc1, ← hw2]
  group

theorem muOne_chi_mul_left {x x' : G} (hx : x ∈ U₁) (hx' : x' ∈ U₁) {r : G} (hr : r ∈ V) :
    r⁻¹ * (x * x' * r * (x * x')⁻¹) = r⁻¹ * (x * r * x⁻¹) * (r⁻¹ * (x' * r * x'⁻¹)) := by
  have h1 := hL.muOne_conj_szA₁ hS hx (hL.conj_V₁ x' hx' r hr)
  calc r⁻¹ * (x * x' * r * (x * x')⁻¹) =
        r⁻¹ * (x * r * x⁻¹) * (x * (r⁻¹ * (x' * r * x'⁻¹)) * x⁻¹) := by group
    _ = _ := by rw [h1]

theorem muOne_chi_mul_right {x : G} (hx : x ∈ U₁) {r r' : G} (hr : r ∈ V) (hr' : r' ∈ V) :
    (r * r')⁻¹ * (x * (r * r') * x⁻¹) = r⁻¹ * (x * r * x⁻¹) * (r'⁻¹ * (x * r' * x⁻¹)) := by
  have e1 : r'⁻¹ * (r⁻¹ * (x * r * x⁻¹)) = (r⁻¹ * (x * r * x⁻¹)) * r'⁻¹ :=
    hS.conf.comm _ (inv_mem hr') _ (hS.conf.le (hL.conj_V₁ x hx r hr))
  calc (r * r')⁻¹ * (x * (r * r') * x⁻¹) = r'⁻¹ * (r⁻¹ * (x * r * x⁻¹)) * (x * r' * x⁻¹) := by
        group
    _ = (r⁻¹ * (x * r * x⁻¹)) * r'⁻¹ * (x * r' * x⁻¹) := by rw [e1]
    _ = _ := by group

theorem muOne_B_mul_left {x x' y : G} (hx : x ∈ U₁) (hx' : x' ∈ U₁) (hy : y ∈ U₁) :
    v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * x' * (y * t * y⁻¹ * t⁻¹) * (x * x')⁻¹)) =
      v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) +
        v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x' * (y * t * y⁻¹ * t⁻¹) * x'⁻¹)) := by
  have hσ := hL.muOne_comm_t_mem hS (hL.U₁_le hy)
  rw [hL.muOne_chi_mul_left hS hc hx hx' hσ,
    hc.mul _ (hL.conj_V₁ x hx _ hσ) _ (hL.conj_V₁ x' hx' _ hσ)]

theorem muOne_B_mul_right {x y y' : G} (hx : x ∈ U₁) (hy : y ∈ U₁) (hy' : y' ∈ U₁) :
    v ((y * y' * t * (y * y')⁻¹ * t⁻¹)⁻¹ * (x * (y * y' * t * (y * y')⁻¹ * t⁻¹) * x⁻¹)) =
      v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) +
        v ((y' * t * y'⁻¹ * t⁻¹)⁻¹ * (x * (y' * t * y'⁻¹ * t⁻¹) * x⁻¹)) := by
  have hb := hL.muOne_comm_t_mem hS (hL.U₁_le hy)
  have hb' := hL.muOne_comm_t_mem hS (hL.U₁_le hy')
  have ha := hL.muOne_conj_V hS hy hb'
  have hcA := hL.conj_V₁ y hy _ hb'
  have e1 : y * (y' * t * y'⁻¹ * t⁻¹) * y⁻¹ = (y' * t * y'⁻¹ * t⁻¹) *
      ((y' * t * y'⁻¹ * t⁻¹)⁻¹ * (y * (y' * t * y'⁻¹ * t⁻¹) * y⁻¹)) := by group
  have hχA : ((y' * t * y'⁻¹ * t⁻¹)⁻¹ * (y * (y' * t * y'⁻¹ * t⁻¹) * y⁻¹))⁻¹ *
      (x * ((y' * t * y'⁻¹ * t⁻¹)⁻¹ * (y * (y' * t * y'⁻¹ * t⁻¹) * y⁻¹)) * x⁻¹) = 1 := by
    rw [hL.muOne_conj_szA₁ hS hx hcA, inv_mul_cancel]
  rw [SzC1.comm_t_mul, hL.muOne_chi_mul_right hS hc hx ha hb, e1,
    hL.muOne_chi_mul_right hS hc hx hb' (hS.conf.le hcA), hχA, mul_one,
    hc.mul _ (hL.conj_V₁ x hx _ hb') _ (hL.conj_V₁ x hx _ hb), add_comm]

theorem muOne_B_eq_zero_left {x : G} (hx : x ∈ U₁) (h0 : v ((x * t * x⁻¹ * t⁻¹) ^ 2) = 0)
    {y : G} (_hy : y ∈ U₁) :
    v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) = 0 := by
  have hxC := hL.muOne_sup_le_centralizer hS (hL.muOne_mem_sup_of_S_eq_zero hS hc hx h0)
  have hσ := hL.muOne_comm_t_mem hS (hL.U₁_le _hy)
  rw [show x * (y * t * y⁻¹ * t⁻¹) * x⁻¹ = y * t * y⁻¹ * t⁻¹ by
    rw [← mem_centralizer_iff.mp hxC _ hσ, mul_inv_cancel_right], inv_mul_cancel, hc.v_one]

theorem muOne_B_eq_zero_right {y : G} (hy : y ∈ U₁) (h0 : v ((y * t * y⁻¹ * t⁻¹) ^ 2) = 0)
    {x : G} (hx : x ∈ U₁) :
    v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) = 0 := by
  obtain ⟨y₀, hy₀, r, hr, rfl⟩ := ncyc_exists_mul_of_mem_sup (hL.muOne_T₁_le_normalizer hS)
    (hL.muOne_mem_sup_of_S_eq_zero hS hc hy h0)
  rw [hL.muOne_comm_t_of_mem_sup hS hy₀ hr, sq, hL.muOne_chi_mul_right hS hc hx hr hr, ← sq,
    hc.sq_eq_one (hL.conj_V₁ x hx r hr), hc.v_one]

theorem muOne_B_conj_d {x y : G} (hx : x ∈ U₁) (hy : y ∈ U₁) :
    v ((d⁻¹ * y * d * t * (d⁻¹ * y * d)⁻¹ * t⁻¹)⁻¹ *
        (d⁻¹ * x * d * (d⁻¹ * y * d * t * (d⁻¹ * y * d)⁻¹ * t⁻¹) * (d⁻¹ * x * d)⁻¹)) =
      μ * v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) := by
  rw [hL.muOne_comm_t_conj_d hS y]
  have e : (d⁻¹ * (y * t * y⁻¹ * t⁻¹) * d)⁻¹ * (d⁻¹ * x * d * (d⁻¹ * (y * t * y⁻¹ * t⁻¹) * d) *
      (d⁻¹ * x * d)⁻¹) = d⁻¹ * ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) * d := by
    group
  rw [e, hc.conj _ (hL.conj_V₁ x hx _ (hL.muOne_comm_t_mem hS (hL.U₁_le hy)))]

theorem muOne_exists_mu (hμV : ¬ U₁ ≤ centralizer (V : Set G)) (hK : Fintype.card K = 2 ^ f)
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) :
    ∃ μ' : K, μ' ≠ 0 ∧ ∀ x ∈ U₁, ∀ y ∈ U₁,
      v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) =
        μ' * (v ((x * t * x⁻¹ * t⁻¹) ^ 2) * v ((y * t * y⁻¹ * t⁻¹) ^ 2)) ^ 2 ^ (f - 1) := by
  obtain ⟨Bf, hBf⟩ := SzC1.exists_addMonoidHom₂_of_hom₂ (M := U₁)
    (S := fun x => v ((x * t * x⁻¹ * t⁻¹) ^ 2))
    (B := fun x y => v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)))
    (fun x hx y hy => hL.muOne_S_mul hS hc hx hy) (hL.muOne_S_surj hS hc hμV hμ)
    (fun x hx x' hx' y hy => hL.muOne_B_mul_left hS hc hx hx' hy)
    (fun x hx y hy y' hy' => hL.muOne_B_mul_right hS hc hx hy hy')
    (fun x hx h0 y hy => hL.muOne_B_eq_zero_left hS hc hx h0 hy)
    (fun y hy h0 x hx => hL.muOne_B_eq_zero_right hS hc hy h0 hx)
  obtain ⟨c, hc'⟩ := bilinear_eq_mul_sqrt_of_equivariant hK
    (by have := hS.start.two_le; omega) Bf hμ fun s s' => by
      obtain ⟨x, hx, rfl⟩ := hL.muOne_S_surj hS hc hμV hμ s
      obtain ⟨y, hy, rfl⟩ := hL.muOne_S_surj hS hc hμV hμ s'
      rw [← hL.muOne_S_conj_d hS hc hx, ← hL.muOne_S_conj_d hS hc hy,
        ← hBf _ (hL.muOne_conj_d_mem_U₁ hS hx) _ (hL.muOne_conj_d_mem_U₁ hS hy), ← hBf x hx y hy]
      exact hL.muOne_B_conj_d hS hc hx hy
  have hform : ∀ x ∈ U₁, ∀ y ∈ U₁,
      v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) =
        c * (v ((x * t * x⁻¹ * t⁻¹) ^ 2) * v ((y * t * y⁻¹ * t⁻¹) ^ 2)) ^ 2 ^ (f - 1) :=
    fun x hx y hy => by rw [hBf x hx y hy, hc']
  refine ⟨c, fun hc0 => hμV fun x hx => mem_centralizer_iff.mpr fun r hr => ?_, hform⟩
  obtain ⟨y, hy, rfl⟩ := hL.muOne_exists_comm_t_eq hS hc hμV hμ hr
  have e := hform x hx y hy
  rw [hc0, zero_mul] at e
  have e1 := hc.eq_one_of_v_eq_zero (hL.conj_V₁ x hx _ (hL.muOne_comm_t_mem hS (hL.U₁_le hy))) e
  calc (y * t * y⁻¹ * t⁻¹) * x =
        (y * t * y⁻¹ * t⁻¹) * ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) * x := by
        rw [e1, mul_one]
    _ = x * (y * t * y⁻¹ * t⁻¹) := by group

theorem muOne_mem_szA₁_of_commute (hμV : ¬ U₁ ≤ centralizer (V : Set G))
    (hK : Fintype.card K = 2 ^ f) (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) {x : G}
    (hx : x ∈ U₁) (hSx : v ((x * t * x⁻¹ * t⁻¹) ^ 2) ≠ 0) {r : G} (hr : r ∈ V)
    (hxr : x * r = r * x) : r ∈ szA₁ (szT₁ L T) := by
  obtain ⟨μ', hμ'0, hform⟩ := hL.muOne_exists_mu hS hc hμV hK hμ
  obtain ⟨y, hy, rfl⟩ := hL.muOne_exists_comm_t_eq hS hc hμV hμ hr
  have e := hform x hx y hy
  rw [show x * (y * t * y⁻¹ * t⁻¹) * x⁻¹ = y * t * y⁻¹ * t⁻¹ by rw [hxr, mul_inv_cancel_right],
    inv_mul_cancel, hc.v_one] at e
  have h1 : (v ((x * t * x⁻¹ * t⁻¹) ^ 2) * v ((y * t * y⁻¹ * t⁻¹) ^ 2)) ^ 2 ^ (f - 1) = 0 :=
    (mul_eq_zero.mp e.symm).resolve_left hμ'0
  have h2 := (mul_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero _ two_ne_zero)).mp h1)).resolve_left hSx
  have hσ := hL.muOne_comm_t_mem hS (hL.U₁_le hy)
  exact hS.conf.omega _ hσ (hc.eq_one_of_v_eq_zero (hL.muOne_sq_mem_szA₁_of_mem_V hS hσ) h2)

theorem muOne_sq_mem_V {x : G} (hx : x ∈ U₁) : x ^ 2 ∈ V := by
  obtain ⟨-, -, -, -, -, hA₁2, -⟩ := hS.start.facts_of_card_sylow hS.card_sylow
  have hS0 : v ((x * x * t * (x * x)⁻¹ * t⁻¹) ^ 2) = 0 := by
    rw [hL.muOne_S_mul hS hc hx hx, CharTwo.add_self_eq_zero]
  obtain ⟨y, hy, r, hr, hyr⟩ := ncyc_exists_mul_of_mem_sup (hL.muOne_T₁_le_normalizer hS)
    (hL.muOne_mem_sup_of_S_eq_zero hS hc (mul_mem hx hx) hS0)
  have hcent : ∀ y₀ ∈ szT₁ L T, y₀ * (x * x) = x * x * y₀ := by
    intro y₀ hy₀
    set a := y₀⁻¹ * (x * y₀ * x⁻¹) with ha
    have haA : a ∈ szA₁ (szT₁ L T) := hL.conj_T₁ x (hL.U₁_le hx) y₀ hy₀
    have hxa : x * a * x⁻¹ = a := hL.muOne_conj_szA₁ hS hx haA
    have ha2 : a * a = 1 := by rw [← sq]; exact hA₁2 a haA
    have e1 : x * y₀ * x⁻¹ = y₀ * a := by rw [ha]; group
    have e2 : x * x * y₀ * (x * x)⁻¹ = y₀ := by
      calc x * x * y₀ * (x * x)⁻¹ = x * (x * y₀ * x⁻¹) * x⁻¹ := by group
        _ = x * (y₀ * a) * x⁻¹ := by rw [e1]
        _ = (x * y₀ * x⁻¹) * (x * a * x⁻¹) := by group
        _ = y₀ * a * a := by rw [e1, hxa]
        _ = y₀ := by rw [mul_assoc, ha2, mul_one]
    calc y₀ * (x * x) = (x * x * y₀ * (x * x)⁻¹) * (x * x) := by rw [e2]
      _ = x * x * y₀ := by group
  have hy' : y = x * x * r⁻¹ := by rw [← hyr]; group
  have hyA : y ∈ szA₁ (szT₁ L T) := by
    refine mem_szA₁.mpr ⟨hy, mem_centralizer_iff.mpr fun y₀ hy₀ => ?_⟩
    calc y₀ * y = y₀ * (x * x) * r⁻¹ := by rw [hy']; group
      _ = x * x * y₀ * r⁻¹ := by rw [hcent y₀ hy₀]
      _ = x * x * (y₀ * r⁻¹) := by group
      _ = x * x * (r⁻¹ * y₀) := by rw [hL.muOne_T₁_comm hS hy₀ (inv_mem hr)]
      _ = y * y₀ := by rw [hy']; group
  rw [sq, ← hyr]
  exact mul_mem (hS.conf.le hyA) hr

theorem muOne_sq_mem_szA₁ (hμV : ¬ U₁ ≤ centralizer (V : Set G))
    (hK : Fintype.card K = 2 ^ f) (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) {x : G}
    (hx : x ∈ U₁) : x ^ 2 ∈ szA₁ (szT₁ L T) := by
  by_cases hSx : v ((x * t * x⁻¹ * t⁻¹) ^ 2) = 0
  · obtain ⟨-, -, -, hsqT, -, -, -⟩ := hS.start.facts_of_card_sylow hS.card_sylow
    obtain ⟨y, hy, r, hr, rfl⟩ := ncyc_exists_mul_of_mem_sup (hL.muOne_T₁_le_normalizer hS)
      (hL.muOne_mem_sup_of_S_eq_zero hS hc hx hSx)
    rw [(Commute.mul_pow (hL.muOne_T₁_comm hS hy hr) 2)]
    exact mul_mem (hsqT y hy) (hL.muOne_sq_mem_szA₁_of_mem_V hS hr)
  · refine hL.muOne_mem_szA₁_of_commute hS hc hμV hK hμ hx hSx (hL.muOne_sq_mem_V hS hc hx) ?_
    rw [sq, mul_assoc]

theorem muOne_mem_V_of_sq_eq_one (hμV : ¬ U₁ ≤ centralizer (V : Set G))
    (hK : Fintype.card K = 2 ^ f) (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) {u : G}
    (hu : u ∈ U₁) (h2 : (u * t) ^ 2 = 1) : u ∈ V := by
  obtain ⟨-, -, -, -, hinvT₁, -, -⟩ := hS.start.facts_of_card_sylow hS.card_sylow
  have htt := hL.muOne_t_mul_self hS
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hu2 := hL.muOne_sq_mem_szA₁ hS hc hμV hK hμ hu
  have e1 : u⁻¹ * t * u⁻¹⁻¹ * t⁻¹ = (u ^ 2)⁻¹ * (u * t) ^ 2 := by
    rw [sq, sq, htinv]; group
  have hσ : u⁻¹ * t * u⁻¹⁻¹ * t⁻¹ ∈ szA₁ (szT₁ L T) := by
    rw [e1, h2, mul_one]
    exact inv_mem hu2
  have hmem := hL.muOne_mem_sup_of_comm_t_mem_szA₁ hS (inv_mem hu) hσ
  obtain ⟨y, hy, r, hr, hyr⟩ := ncyc_exists_mul_of_mem_sup (hL.muOne_T₁_le_normalizer hS)
    (by simpa using inv_mem hmem)
  rw [← hyr, hL.muOne_sq_mul_mul_t hS hy hr] at h2
  rw [← hyr]
  exact mul_mem (hS.conf.le (hinvT₁ y hy h2)) hr

theorem muOne_mem_sup_of_conj (hμV : ¬ U₁ ≤ centralizer (V : Set G))
    (hK : Fintype.card K = 2 ^ f) (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) {P : Subgroup G}
    (hP2 : IsPGroup 2 P) (hUP : U ⊔ T ≤ P) {g : G} (hgP : g ∈ P)
    (hg : g * t * g⁻¹ * t⁻¹ ∈ U₁) : g ∈ U ⊔ T := by
  have htt := hL.muOne_t_mul_self hS
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  set u := g * t * g⁻¹ * t⁻¹ with hu
  have hut : u * t = g * t * g⁻¹ := by rw [hu, htinv, mul_assoc _ t t, htt, mul_one]
  have h2 : (u * t) ^ 2 = 1 := by
    rw [hut, sq, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, htt, mul_one,
      mul_inv_cancel]
  have huV := hL.muOne_mem_V_of_sq_eq_one hS hc hμV hK hμ hg h2
  obtain ⟨w, hw, hwu⟩ := hL.muOne_exists_comm_t_eq hS hc hμV hμ huV
  have hTsyl : IsSylowOf 2 T (centralizer ({t} : Set G)) := by
    obtain ⟨P₀, hP₀⟩ := hS.start.sylow
    exact ⟨P₀, by rw [hP₀, subgroupOf_map_subtype, inf_eq_left.mpr hS.start.le]⟩
  have hc' : (w⁻¹ * g) * t = t * (w⁻¹ * g) := by
    have e : g * t * g⁻¹ = w * t * w⁻¹ := by
      rw [← hut, ← hwu]
      group
    calc (w⁻¹ * g) * t = w⁻¹ * (g * t * g⁻¹) * g := by group
      _ = w⁻¹ * (w * t * w⁻¹) * g := by rw [e]
      _ = t * (w⁻¹ * g) := by group
  have hwP : w ∈ P := hUP (mem_sup_left (hL.U₁_le hw))
  have hH : T ⊔ zpowers (w⁻¹ * g) ≤ centralizer ({t} : Set G) :=
    sup_le hS.start.le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hc'))
  have hHP : T ⊔ zpowers (w⁻¹ * g) ≤ P :=
    sup_le (le_sup_right.trans hUP) (zpowers_le.mpr (mul_mem (inv_mem hwP) hgP))
  have heq := hTsyl.eq_of_le le_sup_left hH (hP2.to_le hHP)
  have hwgT : w⁻¹ * g ∈ T := by
    rw [← heq]
    exact mem_sup_right (mem_zpowers _)
  rw [show g = w * (w⁻¹ * g) by group]
  exact mul_mem (mem_sup_left (hL.U₁_le hw)) (mem_sup_right hwgT)

end Coords

end U3C1OuterLevelData

end CFSG.SeitzReduction.RankOne
