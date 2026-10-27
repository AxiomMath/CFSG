module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterMuOneWeight

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

namespace U3C1OuterLevelData

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G}

section Dich

variable (hS : U3C1OuterStepHyp G L f t T R₂ D d V 1)
  (hL : U3C1OuterLevelData G L f t T D V U U₁ 1) {K : Type} [Field K] [Fintype K] [CharP K 2]
  {v : G → K} {μ : K} (hc : U3A₁Coords (szA₁ (szT₁ L T)) d v μ)
include hS hL hc

theorem muOne_exists_mu_eq_one (hμV : ¬ U₁ ≤ centralizer (V : Set G))
    (hK : Fintype.card K = 2 ^ f) (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) :
    ∀ x ∈ U₁, ∀ y ∈ U₁,
      v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) =
        (v ((x * t * x⁻¹ * t⁻¹) ^ 2) * v ((y * t * y⁻¹ * t⁻¹) ^ 2)) ^ 2 ^ (f - 1) := by
  obtain ⟨μ', -, hform⟩ := hL.muOne_exists_mu hS hc hμV hK hμ
  obtain ⟨u, hu, hSu⟩ := hL.muOne_S_surj hS hc hμV hμ 1
  have hσ := hL.muOne_comm_t_mem hS (hL.U₁_le hu)
  set σu := u * t * u⁻¹ * t⁻¹ with hσu
  have hχA : σu⁻¹ * (u * σu * u⁻¹) ∈ szA₁ (szT₁ L T) := hL.conj_V₁ u hu σu hσ
  have hu2A := hL.muOne_sq_mem_szA₁ hS hc hμV hK hμ hu
  have hu2V : u ^ 2 ∈ V := hS.conf.le hu2A
  have hσu2 : (u * u) * t * (u * u)⁻¹ * t⁻¹ = 1 := by
    rw [← sq, SzC1.comm_eq_sq_of_inv (hS.conf.inv _ hu2V), ← pow_mul]
    obtain ⟨-, -, -, -, -, hA₁2, -⟩ := hS.start.facts_of_card_sylow hS.card_sylow
    have := hA₁2 _ hu2A
    rwa [← pow_mul] at this
  have e1 : (u * u) * t * (u * u)⁻¹ * t⁻¹ = σu ^ 2 * (σu⁻¹ * (u * σu * u⁻¹)) := by
    rw [SzC1.comm_t_mul, ← hσu]
    have hcm : σu * (σu⁻¹ * (u * σu * u⁻¹)) = (σu⁻¹ * (u * σu * u⁻¹)) * σu :=
      hS.conf.comm _ hσ _ (hS.conf.le hχA)
    calc u * σu * u⁻¹ * σu = σu * (σu⁻¹ * (u * σu * u⁻¹)) * σu := by group
      _ = (σu⁻¹ * (u * σu * u⁻¹)) * σu * σu := by rw [hcm]
      _ = σu ^ 2 * (σu⁻¹ * (u * σu * u⁻¹)) := by
          rw [sq, mul_assoc, ← hS.conf.comm _ (mul_mem hσ hσ) _ (hS.conf.le hχA)]
  rw [e1] at hσu2
  have hv0 := congrArg v hσu2
  rw [hc.mul _ (hL.muOne_sq_mem_szA₁_of_mem_V hS hσ) _ hχA, hc.v_one, hSu, hform u hu u hu,
    hSu, one_mul, one_pow, mul_one] at hv0
  have hμ'1 : μ' = 1 := by
    have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination hv0 - h2K
  intro x hx y hy
  rw [hform x hx y hy, hμ'1, one_mul]

theorem muOne_mem_V_of_mem_sup_of_comm {x : G} (hx : x ∈ szT₁ L T ⊔ V)
    (hxC : x ∈ centralizer (szT₁ L T : Set G)) : x ∈ V := by
  obtain ⟨y₁, hy₁, r, hr, rfl⟩ := ncyc_exists_mul_of_mem_sup (hL.muOne_T₁_le_normalizer hS) hx
  have hy₁A : y₁ ∈ szA₁ (szT₁ L T) := by
    refine mem_szA₁.mpr ⟨hy₁, mem_centralizer_iff.mpr fun y₀ hy₀ => ?_⟩
    have hz₀ := mem_centralizer_iff.mp hxC y₀ hy₀
    have hr₀ := hL.muOne_T₁_comm hS hy₀ hr
    calc y₀ * y₁ = y₀ * (y₁ * r) * r⁻¹ := by group
      _ = y₁ * r * y₀ * r⁻¹ := by rw [hz₀]
      _ = y₁ * (r * y₀) * r⁻¹ := by group
      _ = y₁ * (y₀ * r) * r⁻¹ := by rw [hr₀]
      _ = y₁ * y₀ := by group
  exact mul_mem (hS.conf.le hy₁A) hr

theorem muOne_dichotomy (hμV : ¬ U₁ ≤ centralizer (V : Set G)) (hK : Fintype.card K = 2 ^ f)
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) {w : G} (hwT : w ∈ T) (hw2 : w ^ 2 = 1)
    (hwS : w ∉ szT₁ L T ⊔ zpowers t) :
    (∀ r ∈ V, w * r * w⁻¹ = r) ∨ ∀ r ∈ V, w * r * w⁻¹ = r⁻¹ := by
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := hS.start.start_of_card_sylow hS.card_sylow
  obtain ⟨-, hwA, -, -⟩ := hS.start.outer_facts_of_card_sylow hS.card_sylow hwT hw2 hwS
  obtain ⟨-, -, -, -, -, hA₁2, -⟩ := hS.start.facts_of_card_sylow hS.card_sylow
  have hB1 := hL.muOne_exists_mu_eq_one hS hc hμV hK hμ
  have hT₁U₁ : szT₁ L T ≤ U₁ := le_sup_left.trans hL.sup_le_U₁
  have hwt : w * t = t * w := mem_centralizer_singleton_iff.mp (hS.start.le hwT)
  have hwV : ∀ r ∈ V, w * r * w⁻¹ ∈ V := fun r hr =>
    (mem_normalizer_iff.mp (hS.conf.T_le hwT) r).mp hr
  have hwAc : ∀ a ∈ szA₁ (szT₁ L T), w * a * w⁻¹ = a := fun a ha => by
    rw [hwA a ha, mul_inv_cancel_right]
  have hδA : ∀ ρ ∈ V, ρ⁻¹ * (w * ρ * w⁻¹) ∈ szA₁ (szT₁ L T) := by
    intro ρ hρ
    refine hS.conf.omega _ (mul_mem (inv_mem hρ) (hwV ρ hρ)) ?_
    have h2 : (w * ρ * w⁻¹) ^ 2 = ρ ^ 2 := by
      rw [conj_pow, hwAc _ (hL.muOne_sq_mem_szA₁_of_mem_V hS hρ)]
    rw [Commute.mul_pow (hS.conf.comm _ (inv_mem hρ) _ (hwV ρ hρ)) 2, h2, inv_pow,
      inv_mul_cancel]
  have hδmul : ∀ ρ ∈ V, ∀ ρ' ∈ V, (ρ * ρ')⁻¹ * (w * (ρ * ρ') * w⁻¹) =
      (ρ⁻¹ * (w * ρ * w⁻¹)) * (ρ'⁻¹ * (w * ρ' * w⁻¹)) := by
    intro ρ hρ ρ' hρ'
    have c1 : ρ'⁻¹ * (ρ⁻¹ * (w * ρ * w⁻¹)) = (ρ⁻¹ * (w * ρ * w⁻¹)) * ρ'⁻¹ :=
      hS.conf.comm _ (inv_mem hρ') _ (mul_mem (inv_mem hρ) (hwV ρ hρ))
    calc (ρ * ρ')⁻¹ * (w * (ρ * ρ') * w⁻¹) =
          ρ'⁻¹ * (ρ⁻¹ * (w * ρ * w⁻¹)) * (w * ρ' * w⁻¹) := by group
      _ = (ρ⁻¹ * (w * ρ * w⁻¹)) * ρ'⁻¹ * (w * ρ' * w⁻¹) := by rw [c1]
      _ = _ := by group
  have hlam := hL.lambda hS.start hS.card_sylow hS.conf
  have hV₁N : szT₁ L T ≤ normalizer (outerV₁ L T U₁ : Set G) := fun y hy =>
    mem_normalizer_outerV₁ (Subgroup.le_normalizer (hT₁U₁ hy)) (Subgroup.le_normalizer hy)
  have hkey : ∀ ρ ∈ V, ρ⁻¹ * (w * ρ * w⁻¹) = 1 ∨ v (ρ⁻¹ * (w * ρ * w⁻¹)) = v (ρ ^ 2) := by
    intro ρ hρ
    obtain ⟨y, hy, hyρ⟩ := hL.muOne_exists_comm_t_eq hS hc hμV hμ hρ
    rw [hlam] at hy
    obtain ⟨y₀, hy₀, z, hz, rfl⟩ := ncyc_exists_mul_of_mem_sup hV₁N hy
    obtain ⟨hzU, hzC⟩ := mem_outerV₁.mp hz
    have hσz := hL.muOne_comm_t_mem hS (hL.U₁_le hzU)
    have hzρ : z * t * z⁻¹ * t⁻¹ = ρ := by
      rw [← hyρ, SzC1.comm_t_mul, show y₀ * t * y₀⁻¹ * t⁻¹ = 1 by
        rw [mem_centralizer_iff.mp hS.start.mem_centralizer_szT₁ y₀ hy₀]; group, mul_one,
        show y₀ * (z * t * z⁻¹ * t⁻¹) = (z * t * z⁻¹ * t⁻¹) * y₀ from
          hL.muOne_T₁_comm hS hy₀ hσz, mul_inv_cancel_right]
    have hwz : w * z * w⁻¹ ∈ outerV₁ L T U₁ :=
      (mem_normalizer_iff.mp (mem_normalizer_outerV₁ (hL.T_le hwT) (hTN₁ hwT)) z).mp hz
    have hwzU := (mem_outerV₁.mp hwz).1
    set r := (w * z * w⁻¹) * z⁻¹ with hrdef
    have hσw : (w * z * w⁻¹) * t * (w * z * w⁻¹)⁻¹ * t⁻¹ = w * (z * t * z⁻¹ * t⁻¹) * w⁻¹ := by
      have hwtw : w * t * w⁻¹ = t := by rw [hwt, mul_inv_cancel_right]
      calc (w * z * w⁻¹) * t * (w * z * w⁻¹)⁻¹ * t⁻¹ =
            (w * z * w⁻¹) * (w * t * w⁻¹) * (w * z * w⁻¹)⁻¹ * (w * t * w⁻¹)⁻¹ := by rw [hwtw]
        _ = w * (z * t * z⁻¹ * t⁻¹) * w⁻¹ := by group
    have hSw : v (((w * z * w⁻¹) * t * (w * z * w⁻¹)⁻¹ * t⁻¹) ^ 2) =
        v ((z * t * z⁻¹ * t⁻¹) ^ 2) := by
      rw [hσw, conj_pow, hwAc _ (hL.muOne_sq_mem_szA₁_of_mem_V hS hσz)]
    have hSinv : v ((z⁻¹ * t * z⁻¹⁻¹ * t⁻¹) ^ 2) = v ((z * t * z⁻¹ * t⁻¹) ^ 2) := by
      have h1 := hL.muOne_S_mul hS hc (inv_mem hzU) hzU
      rw [inv_mul_cancel, show (1 : G) * t * (1 : G)⁻¹ * t⁻¹ = 1 by group, one_pow,
        hc.v_one] at h1
      have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination -h1 - v ((z * t * z⁻¹ * t⁻¹) ^ 2) * h2K
    have hrU : r ∈ U₁ := mul_mem hwzU (inv_mem hzU)
    have hSr : v ((r * t * r⁻¹ * t⁻¹) ^ 2) = 0 := by
      rw [hrdef, hL.muOne_S_mul hS hc hwzU (inv_mem hzU), hSw, hSinv, CharTwo.add_self_eq_zero]
    have hrC : r ∈ centralizer (szT₁ L T : Set G) :=
      mul_mem (mem_outerV₁.mp hwz).2 (inv_mem hzC)
    have hrV : r ∈ V := hL.muOne_mem_V_of_mem_sup_of_comm hS hc
      (hL.muOne_mem_sup_of_S_eq_zero hS hc hrU hSr) hrC
    have hz2 := hL.muOne_sq_mem_szA₁ hS hc hμV hK hμ hzU
    have hrz : w * z * w⁻¹ = r * z := by rw [hrdef]; group
    have hwz2 : (r * z) ^ 2 = z ^ 2 := by rw [← hrz, conj_pow, hwAc _ hz2]
    set χ := r⁻¹ * (z * r * z⁻¹) with hχ
    have e1 : (r * z) ^ 2 = r ^ 2 * χ * z ^ 2 := by rw [hχ, sq, sq, sq]; group
    have e2 : r ^ 2 * χ = 1 := by
      have h3 := hwz2
      rw [e1] at h3
      exact mul_right_cancel (h3.trans (one_mul _).symm)
    have hr2A := hL.muOne_sq_mem_szA₁_of_mem_V hS hrV
    have hχeq : χ = r ^ 2 := by
      have h4 : (r ^ 2)⁻¹ = r ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hA₁2 _ hr2A)
      rw [← h4]
      exact eq_inv_of_mul_eq_one_right e2
    have hδ : ρ⁻¹ * (w * ρ * w⁻¹) = r ^ 2 := by
      have h5 : w * ρ * w⁻¹ = ρ * r ^ 2 := by
        rw [← hzρ, ← hσw, hrz, SzC1.comm_t_mul, SzC1.comm_eq_sq_of_inv (hS.conf.inv r hrV),
          show r * (z * t * z⁻¹ * t⁻¹) * r⁻¹ = z * t * z⁻¹ * t⁻¹ by
            rw [hS.conf.comm r hrV _ hσz, mul_inv_cancel_right]]
      rw [h5, inv_mul_cancel_left]
    obtain ⟨y', hy', hy'r⟩ := hL.muOne_exists_comm_t_eq hS hc hμV hμ hrV
    have hB := hB1 z hzU y' hy'
    rw [hy'r] at hB
    have hχv : v χ = v (r ^ 2) := by rw [hχeq]
    rw [← hχ, hχv] at hB
    set ξ := v (r ^ 2) with hξ
    set s := v ((z * t * z⁻¹ * t⁻¹) ^ 2) with hs
    have hfrob : ((s * ξ) ^ 2 ^ (f - 1)) ^ 2 = s * ξ := by
      rw [← pow_mul, ← pow_succ, show f - 1 + 1 = f by have := hS.start.two_le; omega, ← hK,
        FiniteField.pow_card]
    have hξ2 : ξ * (ξ - s) = 0 := by
      have h6 : ξ ^ 2 = s * ξ := by
        calc ξ ^ 2 = ((s * ξ) ^ 2 ^ (f - 1)) ^ 2 := by conv_lhs => rw [hB]
          _ = s * ξ := hfrob
      linear_combination h6
    rcases mul_eq_zero.mp hξ2 with h0 | h0
    · left
      rw [hδ]
      exact hc.eq_one_of_v_eq_zero hr2A h0
    · right
      rw [hδ, ← hzρ]
      exact (sub_eq_zero.mp h0).trans rfl
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨ρ₀, hρ₀, h0⟩, ⟨ρ₁, hρ₁, h1⟩⟩ := hcon
  have hρ₀δ : ρ₀⁻¹ * (w * ρ₀ * w⁻¹) ≠ 1 := fun h => h0 (by
    rw [show w * ρ₀ * w⁻¹ = ρ₀ * (ρ₀⁻¹ * (w * ρ₀ * w⁻¹)) by group, h, mul_one])
  have hρ₀v := (hkey ρ₀ hρ₀).resolve_left hρ₀δ
  have hρ₁sq : ρ₁ ^ 2 ∈ szA₁ (szT₁ L T) := hL.muOne_sq_mem_szA₁_of_mem_V hS hρ₁
  have hρ₁v : v (ρ₁⁻¹ * (w * ρ₁ * w⁻¹)) ≠ v (ρ₁ ^ 2) := fun h => h1 (by
    have e := hc.inj _ (hδA ρ₁ hρ₁) _ hρ₁sq h
    have h4 : (ρ₁ ^ 2)⁻¹ = ρ₁ ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hA₁2 _ hρ₁sq)
    calc w * ρ₁ * w⁻¹ = ρ₁ * (ρ₁⁻¹ * (w * ρ₁ * w⁻¹)) := by group
      _ = ρ₁ * ρ₁ ^ 2 := by rw [e]
      _ = ρ₁ * (ρ₁ ^ 2)⁻¹ := by rw [h4]
      _ = ρ₁⁻¹ := by rw [sq]; group)
  have hρ₁δ := (hkey ρ₁ hρ₁).resolve_right hρ₁v
  rcases hkey (ρ₀ * ρ₁) (mul_mem hρ₀ hρ₁) with h2 | h2
  · rw [hδmul ρ₀ hρ₀ ρ₁ hρ₁, hρ₁δ, mul_one] at h2
    exact hρ₀δ h2
  · rw [hδmul ρ₀ hρ₀ ρ₁ hρ₁, hρ₁δ, mul_one, hρ₀v,
      Commute.mul_pow (hS.conf.comm ρ₀ hρ₀ ρ₁ hρ₁) 2,
      hc.mul _ (hL.muOne_sq_mem_szA₁_of_mem_V hS hρ₀) _ hρ₁sq] at h2
    have h7 : v (ρ₁ ^ 2) = 0 := by linear_combination -h2
    apply hρ₁v
    rw [hρ₁δ, hc.v_one, h7]

end Dich

end U3C1OuterLevelData

end CFSG.SeitzReduction.RankOne
