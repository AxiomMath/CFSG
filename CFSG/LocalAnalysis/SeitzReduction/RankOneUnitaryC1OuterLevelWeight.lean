module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterLevelStage
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1Level

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1OuterStage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ}

section Coords

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {v : G → K}
  {μ : K} (h : U3C1OuterStage G L f t T d V U U₁ k) (hK : Fintype.card K = 2 ^ f)
  (hc : U3A₁Coords (szA₁ (szT₁ L T)) d v μ)
include h hK hc

theorem B_mul_left {x x' y : G} (hx : x ∈ U₁) (hx' : x' ∈ U₁) (hy : y ∈ U₁) :
    v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * x' * (y * t * y⁻¹ * t⁻¹) * (x * x')⁻¹)) =
      v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) +
        v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x' * (y * t * y⁻¹ * t⁻¹) * x'⁻¹)) := by
  have hσ := h.comm_t_mem (h.U₁_le hy)
  rw [h.chi_mul_left hx hx' hσ, hc.mul _ (h.conj_V₁ x hx _ hσ) _ (h.conj_V₁ x' hx' _ hσ)]

theorem B_mul_right {x y y' : G} (hx : x ∈ U₁) (hy : y ∈ U₁) (hy' : y' ∈ U₁) :
    v ((y * y' * t * (y * y')⁻¹ * t⁻¹)⁻¹ * (x * (y * y' * t * (y * y')⁻¹ * t⁻¹) * x⁻¹)) =
      v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) +
        v ((y' * t * y'⁻¹ * t⁻¹)⁻¹ * (x * (y' * t * y'⁻¹ * t⁻¹) * x⁻¹)) := by
  have hb := h.comm_t_mem (h.U₁_le hy)
  have hb' := h.comm_t_mem (h.U₁_le hy')
  have ha := h.conj_V hy hb'
  have hcA := h.conj_V₁ y hy _ hb'
  have e1 : y * (y' * t * y'⁻¹ * t⁻¹) * y⁻¹ = (y' * t * y'⁻¹ * t⁻¹) *
      ((y' * t * y'⁻¹ * t⁻¹)⁻¹ * (y * (y' * t * y'⁻¹ * t⁻¹) * y⁻¹)) := by group
  rw [SzC1.comm_t_mul, h.chi_mul_right hx ha hb, e1, h.chi_mul_right hx hb' (h.le hcA),
    h.chi_eq_one_of_mem_szA₁ hx hcA, mul_one,
    hc.mul _ (h.conj_V₁ x hx _ hb') _ (h.conj_V₁ x hx _ hb), add_comm]

theorem B_eq_zero_left {x : G} (hx : x ∈ U₁) (h0 : v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k) = 0)
    {y : G} (hy : y ∈ U₁) : v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) = 0 := by
  rw [h.chi_eq_one_of_mem_sup (h.mem_sup_of_S_eq_zero hK hc hx h0) (h.comm_t_mem (h.U₁_le hy)),
    hc.v_one]

theorem B_eq_zero_right {y : G} (hy : y ∈ U₁) (h0 : v ((y * t * y⁻¹ * t⁻¹) ^ 2 ^ k) = 0)
    {x : G} (hx : x ∈ U₁) : v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) = 0 := by
  obtain ⟨y₀, hy₀, r, hr, rfl⟩ := h.exists_mul_of_mem_sup (h.mem_sup_of_S_eq_zero hK hc hy h0)
  rw [h.comm_t_of_mem_sup hy₀ hr, sq, h.chi_mul_right hx hr hr, ← sq,
    hc.sq_eq_one (h.conj_V₁ x hx r hr), hc.v_one]

theorem B_conj_d {x y : G} (hx : x ∈ U₁) (hy : y ∈ U₁) :
    v ((d⁻¹ * y * d * t * (d⁻¹ * y * d)⁻¹ * t⁻¹)⁻¹ *
        (d⁻¹ * x * d * (d⁻¹ * y * d * t * (d⁻¹ * y * d)⁻¹ * t⁻¹) * (d⁻¹ * x * d)⁻¹)) =
      μ * v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) := by
  rw [h.comm_t_conj_d y]
  have e : (d⁻¹ * (y * t * y⁻¹ * t⁻¹) * d)⁻¹ * (d⁻¹ * x * d * (d⁻¹ * (y * t * y⁻¹ * t⁻¹) * d) *
      (d⁻¹ * x * d)⁻¹) = d⁻¹ * ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) * d := by
    group
  rw [e, hc.conj _ (h.conj_V₁ x hx _ (h.comm_t_mem (h.U₁_le hy)))]

theorem exists_mu (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) :
    ∃ μ' : K, ∀ x ∈ U₁, ∀ y ∈ U₁,
      v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) =
        μ' * (v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k) * v ((y * t * y⁻¹ * t⁻¹) ^ 2 ^ k)) ^ 2 ^ (f - 1) := by
  obtain ⟨D, hD⟩ := SzC1.exists_addMonoidHom₂_of_hom₂ (M := U₁)
    (S := fun x => v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k))
    (B := fun x y => v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)))
    (fun x hx y hy => h.S_mul hK hc hx hy) (h.S_surj hK hc hμ)
    (fun x hx x' hx' y hy => h.B_mul_left hK hc hx hx' hy)
    (fun x hx y hy y' hy' => h.B_mul_right hK hc hx hy hy')
    (fun x hx h0 y hy => h.B_eq_zero_left hK hc hx h0 hy)
    (fun y hy h0 x hx => h.B_eq_zero_right hK hc hy h0 hx)
  obtain ⟨c, hc'⟩ := bilinear_eq_mul_sqrt_of_equivariant hK (by have := h.start.two_le; omega) D
    hμ fun s s' => by
      obtain ⟨x, hx, rfl⟩ := h.S_surj hK hc hμ s
      obtain ⟨y, hy, rfl⟩ := h.S_surj hK hc hμ s'
      rw [← h.S_conj_d hK hc hx, ← h.S_conj_d hK hc hy,
        ← hD _ (h.conj_d_mem_U₁ hx) _ (h.conj_d_mem_U₁ hy), ← hD x hx y hy]
      exact h.B_conj_d hK hc hx hy
  exact ⟨c, fun x hx y hy => by rw [hD x hx y hy, hc']⟩

end Coords

theorem comm_mem_szA₁ (h : U3C1OuterStage G L f t T d V U U₁ k) :
    ∀ x ∈ U₁, ∀ y ∈ U₁, x * y * x⁻¹ * y⁻¹ ∈ szA₁ (szT₁ L T) := by
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := h.coords
  obtain ⟨μ', hμ'⟩ := h.exists_mu hK hc hμ
  intro x hx y hy
  have hxU := h.U₁_le hx
  have hyU := h.U₁_le hy
  have hσx := h.comm_t_mem hxU
  have hσy := h.comm_t_mem hyU
  have hχx := h.conj_V₁ x hx _ hσy
  have hχy := h.conj_V₁ y hy _ hσx
  have hsym : (y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹) =
      (x * t * x⁻¹ * t⁻¹)⁻¹ * (y * (x * t * x⁻¹ * t⁻¹) * y⁻¹) :=
    hc.inj _ hχx _ hχy
      (by rw [hμ' x hx y hy, hμ' y hy x hx, mul_comm (v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k))])
  set c := x * y * x⁻¹ * y⁻¹ with hcdef
  have hcU₁ : c ∈ U₁ := mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have hcV : ∀ r ∈ V, c * r * c⁻¹ = r := fun r hr =>
    SzC1.comm_conj_eq_of_dev h.szA₁_comm (h.conj_szA₁ x hxU) (h.conj_szA₁ y hyU)
      (h.conj_V₁ x hx r hr) (h.conj_V₁ y hy r hr)
  set P := (y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹) with hP
  have hPV : P ∈ V := h.le hχx
  have e1 : x * y * t * (x * y)⁻¹ * t⁻¹ = (y * t * y⁻¹ * t⁻¹) * P * (x * t * x⁻¹ * t⁻¹) := by
    rw [SzC1.comm_t_mul, hP]
    group
  have e2 : y * x * t * (y * x)⁻¹ * t⁻¹ = (x * t * x⁻¹ * t⁻¹) * P * (y * t * y⁻¹ * t⁻¹) := by
    rw [SzC1.comm_t_mul, hsym]
    group
  have e3 : (y * t * y⁻¹ * t⁻¹) * P * (x * t * x⁻¹ * t⁻¹) =
      (x * t * x⁻¹ * t⁻¹) * P * (y * t * y⁻¹ * t⁻¹) := by
    rw [mul_assoc, h.comm P hPV _ hσx, ← mul_assoc, h.comm _ hσy _ hσx, mul_assoc,
      h.comm _ hσy P hPV, ← mul_assoc]
  have e4 : x * y * t * (x * y)⁻¹ * t⁻¹ =
      (y * x * t * (y * x)⁻¹ * t⁻¹) * (c * t * c⁻¹ * t⁻¹) := by
    have h4 := SzC1.comm_t_mul c (y * x) t
    rw [show c * (y * x) = x * y by rw [hcdef]; group] at h4
    rw [h4, hcV _ (h.comm_t_mem (mul_mem hyU hxU))]
  rw [e1, e3, ← e2] at e4
  have hσc : c * t * c⁻¹ * t⁻¹ = 1 := (mul_eq_left.mp e4.symm)
  have hct : c * t = t * c := by
    calc c * t = (c * t * c⁻¹ * t⁻¹) * t * c := by group
      _ = t * c := by rw [hσc, one_mul]
  have hcT₁ := h.mem_T₁_of_comm hcU₁ hct
  refine mem_szA₁.mpr ⟨hcT₁, mem_centralizer_iff.mpr fun y₀ hy₀ => ?_⟩
  have h5 := SzC1.comm_conj_eq_of_dev h.szA₁_comm (h.conj_szA₁ x hxU) (h.conj_szA₁ y hyU)
    (h.conj_T₁ x hxU y₀ hy₀) (h.conj_T₁ y hyU y₀ hy₀)
  rw [← hcdef] at h5
  calc y₀ * c = (c * y₀ * c⁻¹) * c := by rw [h5]
    _ = c * y₀ := by group

theorem sq_mem_V (h : U3C1OuterStage G L f t T d V U U₁ k) {x : G}
    (hx : x ∈ U₁) : x ^ 2 ∈ V := by
  obtain ⟨K, _, _, _, v, μ, hK, hc, -⟩ := h.coords
  have hxU := h.U₁_le hx
  have hS : v ((x * x * t * (x * x)⁻¹ * t⁻¹) ^ 2 ^ k) = 0 := by
    rw [h.S_mul hK hc hx hx, CharTwo.add_self_eq_zero]
  obtain ⟨y, hy, r, hr, hyr⟩ :=
    h.exists_mul_of_mem_sup (h.mem_sup_of_S_eq_zero hK hc (mul_mem hx hx) hS)
  have hcent : ∀ y₀ ∈ szT₁ L T, y₀ * (x * x) = x * x * y₀ := by
    intro y₀ hy₀
    have e := h.delta_mul_left hxU hxU hy₀
    have hδ := hc.sq_eq_one (h.conj_T₁ x hxU y₀ hy₀)
    rw [sq] at hδ
    rw [hδ] at e
    have e2 : x * x * y₀ * (x * x)⁻¹ = y₀ := by
      calc x * x * y₀ * (x * x)⁻¹ = y₀ * (y₀⁻¹ * (x * x * y₀ * (x * x)⁻¹)) := by group
        _ = y₀ := by rw [e, mul_one]
    calc y₀ * (x * x) = (x * x * y₀ * (x * x)⁻¹) * (x * x) := by rw [e2]
      _ = x * x * y₀ := by group
  have hy' : y = x * x * r⁻¹ := by rw [hyr]; group
  have hyA : y ∈ szA₁ (szT₁ L T) := by
    refine mem_szA₁.mpr ⟨hy, mem_centralizer_iff.mpr fun y₀ hy₀ => ?_⟩
    calc y₀ * y = y₀ * (x * x) * r⁻¹ := by rw [hy']; group
      _ = x * x * y₀ * r⁻¹ := by rw [hcent y₀ hy₀]
      _ = x * x * (y₀ * r⁻¹) := by group
      _ = x * x * (r⁻¹ * y₀) := by rw [h.V_comm (inv_mem hr) hy₀]
      _ = y * y₀ := by rw [hy']; group
  rw [sq, hyr]
  exact mul_mem (h.le hyA) hr

section Coords

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {v : G → K}
  {μ : K} (h : U3C1OuterStage G L f t T d V U U₁ k) (hK : Fintype.card K = 2 ^ f)
  (hc : U3A₁Coords (szA₁ (szT₁ L T)) d v μ)
include h hK hc

theorem mu_eq_zero_or_one (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) :
    ∃ μ' : K, (μ' = 0 ∨ μ' = 1) ∧ (2 ≤ k → μ' = 0) ∧ ∀ x ∈ U₁, ∀ y ∈ U₁,
      v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) =
        μ' * (v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k) * v ((y * t * y⁻¹ * t⁻¹) ^ 2 ^ k)) ^ 2 ^ (f - 1) := by
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨μ', hμ'⟩ := h.exists_mu hK hc hμ
  obtain ⟨u₀, hu₀, hS1⟩ := h.S_surj hK hc hμ 1
  have hsqV := h.sq_mem_V hu₀
  obtain ⟨y₀, hy₀, hy₀σ⟩ := h.exists_comm_t_eq hK hc hμ hsqV
  have hB0 := hμ' u₀ hu₀ y₀ hy₀
  rw [hy₀σ, show u₀ * u₀ ^ 2 * u₀⁻¹ = u₀ ^ 2 by group, inv_mul_cancel, hc.v_one, hS1,
    one_mul] at hB0
  have hσuV := h.comm_t_mem (h.U₁_le hu₀)
  obtain ⟨σu, hσu⟩ : ∃ σu, σu = u₀ * t * u₀⁻¹ * t⁻¹ := ⟨_, rfl⟩
  rw [← hσu] at hσuV hS1
  have hχA : σu⁻¹ * (u₀ * σu * u₀⁻¹) ∈ szA₁ (szT₁ L T) := h.conj_V₁ u₀ hu₀ σu hσuV
  have hBuu := hμ' u₀ hu₀ u₀ hu₀
  rw [← hσu, hS1, one_mul, one_pow, mul_one] at hBuu
  have e1 : (u₀ ^ 2) ^ 2 = σu ^ 2 * (σu⁻¹ * (u₀ * σu * u₀⁻¹)) := by
    rw [← h.comm_t_of_mem_V hsqV, sq u₀, SzC1.comm_t_mul, ← hσu]
    rw [show u₀ * σu * u₀⁻¹ * σu = σu * (σu⁻¹ * (u₀ * σu * u₀⁻¹)) * σu by group, mul_assoc,
      h.comm _ (h.le hχA) σu hσuV, ← mul_assoc, ← sq]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := h.one_le; omega⟩
  have e2 : (u₀ ^ 2) ^ 2 ^ (j + 1) =
      σu ^ 2 ^ (j + 1) * (σu⁻¹ * (u₀ * σu * u₀⁻¹)) ^ 2 ^ j := by
    calc (u₀ ^ 2) ^ 2 ^ (j + 1) = ((u₀ ^ 2) ^ 2) ^ 2 ^ j := by
          rw [← pow_mul (u₀ ^ 2) 2 (2 ^ j), ← pow_succ']
      _ = _ := by
        rw [e1, (Commute.mul_pow (h.comm _ (pow_mem hσuV 2) _ (h.le hχA)) _), ← pow_mul,
          ← pow_succ']
  rw [e2] at hB0
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    simp only [zero_add, pow_zero, pow_one] at hB0 hS1
    have hσ2 : σu ^ 2 ∈ szA₁ (szT₁ L T) := by simpa using h.pow_mem_szA₁ hσuV
    rw [hc.mul _ hσ2 _ hχA, hS1, hBuu] at hB0
    refine ⟨μ', ?_, fun h2 => absurd h2 (by norm_num), hμ'⟩
    rcases mul_eq_zero.mp hB0.symm with h0 | h0
    · exact Or.inl h0
    · right
      have h3 := pow_eq_zero_iff ((pow_ne_zero (f - 1) two_ne_zero)) |>.mp h0
      linear_combination h3 - h2K
  · have hχ1 : (σu⁻¹ * (u₀ * σu * u₀⁻¹)) ^ 2 ^ j = 1 := by
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [pow_succ', pow_mul, hc.sq_eq_one hχA, one_pow]
    rw [hχ1, mul_one, hS1, one_pow, mul_one] at hB0
    exact ⟨μ', Or.inl hB0.symm, fun _ => hB0.symm, hμ'⟩

end Coords

end U3C1OuterStage

namespace U3C1OuterStage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ}

section Basic

variable (h : U3C1OuterStage G L f t T d V U U₁ k)
include h

theorem V_le_V₁ : V ≤ U₁ ⊓ centralizer (szT₁ L T : Set G) :=
  le_inf h.V_le_U₁ h.le_centralizer

theorem mem_V_of_mem_V₁_of_mem_sup {w : G} (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hws : w ∈ szT₁ L T ⊔ V) : w ∈ V := by
  obtain ⟨y, hy, r, hr, rfl⟩ := h.exists_mul_of_mem_sup hws
  have hyC : y ∈ centralizer (szT₁ L T : Set G) := by
    have := mul_mem (mem_inf.mp hw).2 (h.le_centralizer (inv_mem hr))
    simpa using this
  exact mul_mem (h.le (mem_szA₁.mpr ⟨hy, hyC⟩)) hr

theorem conj_d_mem_V₁ {w : G} (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    d⁻¹ * w * d ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) := by
  obtain ⟨hwU₁, hwC⟩ := mem_inf.mp hw
  refine mem_inf.mpr ⟨h.conj_d_mem_U₁ hwU₁, mem_centralizer_iff.mpr fun y hy => ?_⟩
  have hdy : d * y * d⁻¹ ∈ szT₁ L T := by
    simpa using (mem_normalizer_iff.mp h.d_norm.1.2 y).mp hy
  have e := mem_centralizer_iff.mp hwC _ hdy
  calc y * (d⁻¹ * w * d) = d⁻¹ * ((d * y * d⁻¹) * w) * d := by group
    _ = d⁻¹ * (w * (d * y * d⁻¹)) * d := by rw [e]
    _ = d⁻¹ * w * d * y := by group

theorem sq_mul_t (x : G) : (x * t) ^ 2 = x * (t * x * t⁻¹) := by
  rw [sq, h.t_inv]
  group

theorem t_conj_mem_V₁ {w : G} (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    t * w * t⁻¹ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) := by
  obtain ⟨hwU₁, hwC⟩ := mem_inf.mp hw
  refine mem_inf.mpr ⟨h.conj_mem_U₁ h.t_mem_U hwU₁, mem_centralizer_iff.mpr fun y hy => ?_⟩
  have e := mem_centralizer_iff.mp hwC y hy
  have e1 : y * t = t * y := h.t_comm hy
  have e2 : y * t⁻¹ = t⁻¹ * y := by rw [h.t_inv]; exact e1
  calc y * (t * w * t⁻¹) = (y * t) * w * t⁻¹ := by group
    _ = t * (y * w) * t⁻¹ := by rw [e1]; group
    _ = t * (w * y) * t⁻¹ := by rw [e]
    _ = t * w * (y * t⁻¹) := by group
    _ = t * w * (t⁻¹ * y) := by rw [e2]
    _ = t * w * t⁻¹ * y := by group

theorem U_le_normalizer_sup : U ≤ normalizer ((szT₁ L T ⊔ V : Subgroup G) : Set G) :=
  fun x hx => mem_normalizer_of_forall_inv_mul_mul_mem fun z hz => by
    obtain ⟨y, hy, r, hr, rfl⟩ := h.exists_mul_of_mem_sup hz
    rw [show x⁻¹ * (y * r) * x = (x⁻¹ * y * x⁻¹⁻¹) * (x⁻¹ * r * x⁻¹⁻¹) by group]
    exact mul_mem (mem_sup_left (h.conj_T₁_mem (inv_mem hx) hy))
      (mem_sup_right (h.conj_V_of_mem_U (inv_mem hx) hr))

end Basic

section Coords

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {v : G → K}
  {μ : K} (h : U3C1OuterStage G L f t T d V U U₁ k) (hK : Fintype.card K = 2 ^ f)
  (hc : U3A₁Coords (szA₁ (szT₁ L T)) d v μ)
include h hK hc

theorem S_surj_V₁ (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w)
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) (s : K) :
    ∃ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), v ((w * t * w⁻¹ * t⁻¹) ^ 2 ^ k) = s := by
  obtain ⟨x, hx, hxs⟩ := h.S_surj hK hc hμ s
  have hTN : szT₁ L T ≤ normalizer ((U₁ ⊓ centralizer (szT₁ L T : Set G) : Subgroup G) : Set G) :=
    fun y hy => mem_normalizer_of_forall_inv_mul_mul_mem fun w hw => by
      rw [mem_centralizer_iff.mp (mem_inf.mp hw).2 _ (inv_mem hy), inv_mul_cancel_right]
      exact hw
  have hx' : x ∈ ((szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)) : Subgroup G) : Set G) := by
    rw [← hlam]
    exact hx
  rw [coe_mul_of_left_le_normalizer_right _ _ hTN] at hx'
  obtain ⟨y, hy, w, hw, rfl⟩ := hx'
  refine ⟨w, hw, ?_⟩
  rw [← hxs, h.S_mul hK hc (h.T₁_le_U₁ hy) (mem_inf.mp hw).1,
    h.S_eq_zero_of_mem_sup hK hc (mem_sup_left hy), zero_add]

theorem V₁_comm' (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w)
    (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) :
    ∀ x ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), ∀ y ∈ U₁ ⊓ centralizer (szT₁ L T : Set G),
      x * y = y * x := by
  set V₁ := U₁ ⊓ centralizer (szT₁ L T : Set G) with hV₁
  have hcA : ∀ x ∈ V₁, ∀ y ∈ V₁, x * y * x⁻¹ * y⁻¹ ∈ szA₁ (szT₁ L T) := fun x hx y hy =>
    h.comm_mem_szA₁ x (mem_inf.mp hx).1 y (mem_inf.mp hy).1
  have hcen : ∀ x ∈ V₁, ∀ b ∈ szA₁ (szT₁ L T), x * b * x⁻¹ = b := fun x hx b hb =>
    h.conj_szA₁ x (h.U₁_le (mem_inf.mp hx).1) b hb
  have hVc : ∀ x ∈ V₁, x ∈ V → ∀ y ∈ V₁, x * y * x⁻¹ * y⁻¹ = 1 := by
    intro x _ hxV y hy
    rw [mem_centralizer_iff.mp (hμV (mem_inf.mp hy).1) x hxV]
    group
  obtain ⟨D, hD⟩ := SzC1.exists_addMonoidHom₂_of_hom₂ (M := V₁)
    (S := fun x => v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k)) (B := fun x y => v (x * y * x⁻¹ * y⁻¹))
    (fun x hx y hy => h.S_mul hK hc (mem_inf.mp hx).1 (mem_inf.mp hy).1)
    (h.S_surj_V₁ hK hc hμ hlam)
    (fun x hx x' hx' y hy => by
      show v (x * x' * y * (x * x')⁻¹ * y⁻¹) = v (x * y * x⁻¹ * y⁻¹) + v (x' * y * x'⁻¹ * y⁻¹)
      rw [show x * x' * y * (x * x')⁻¹ * y⁻¹ = x * (x' * y * x'⁻¹ * y⁻¹) * x⁻¹ *
          (x * y * x⁻¹ * y⁻¹) by group, hcen x hx _ (hcA x' hx' y hy),
        hc.mul _ (hcA x' hx' y hy) _ (hcA x hx y hy), add_comm])
    (fun x hx y hy y' hy' => by
      show v (x * (y * y') * x⁻¹ * (y * y')⁻¹) = v (x * y * x⁻¹ * y⁻¹) + v (x * y' * x⁻¹ * y'⁻¹)
      rw [show x * (y * y') * x⁻¹ * (y * y')⁻¹ = x * y * x⁻¹ * y⁻¹ *
          (y * (x * y' * x⁻¹ * y'⁻¹) * y⁻¹) by group, hcen y hy _ (hcA x hx y' hy'),
        hc.mul _ (hcA x hx y hy) _ (hcA x hx y' hy')])
    (fun x hx h0 y hy => by
      show v (x * y * x⁻¹ * y⁻¹) = 0
      rw [hVc x hx (h.mem_V_of_mem_V₁_of_mem_sup hx (h.mem_sup_of_S_eq_zero hK hc
        (mem_inf.mp hx).1 h0)) y hy, hc.v_one])
    (fun y hy h0 x hx => by
      show v (x * y * x⁻¹ * y⁻¹) = 0
      have hyV := h.mem_V_of_mem_V₁_of_mem_sup hy (h.mem_sup_of_S_eq_zero hK hc
        (mem_inf.mp hy).1 h0)
      rw [show x * y * x⁻¹ * y⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ by group, hVc y hy hyV x hx, inv_one,
        hc.v_one])
  obtain ⟨c, hc'⟩ := bilinear_eq_mul_sqrt_of_equivariant hK (by have := h.start.two_le; omega) D
    hμ fun s s' => by
      obtain ⟨x, hx, rfl⟩ := h.S_surj_V₁ hK hc hμ hlam s
      obtain ⟨y, hy, rfl⟩ := h.S_surj_V₁ hK hc hμ hlam s'
      rw [← h.S_conj_d hK hc (mem_inf.mp hx).1, ← h.S_conj_d hK hc (mem_inf.mp hy).1,
        ← hD _ (h.conj_d_mem_V₁ hx) _ (h.conj_d_mem_V₁ hy), ← hD x hx y hy]
      rw [show d⁻¹ * x * d * (d⁻¹ * y * d) * (d⁻¹ * x * d)⁻¹ * (d⁻¹ * y * d)⁻¹ =
        d⁻¹ * (x * y * x⁻¹ * y⁻¹) * d by group, hc.conj _ (hcA x hx y hy)]
  obtain ⟨x₁, hx₁, hS₁⟩ := h.S_surj_V₁ hK hc hμ hlam 1
  have hc0 : c = 0 := by
    have e := (hD x₁ hx₁ x₁ hx₁).trans (hc' _ _)
    rw [show x₁ * x₁ * x₁⁻¹ * x₁⁻¹ = (1 : G) by group, hc.v_one, hS₁, one_mul, one_pow,
      mul_one] at e
    exact e.symm
  intro x hx y hy
  have e := (hD x hx y hy).trans (hc' _ _)
  rw [hc0, zero_mul] at e
  have e1 := hc.eq_one_of_v_eq_zero (hcA x hx y hy) e
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [e1, one_mul]

theorem sq_mul_t_mem_szA₁ (hμV : U₁ ≤ centralizer (V : Set G)) {w : G} (hw : w ∈ U₁) :
    (w * t) ^ 2 ∈ szA₁ (szT₁ L T) := by
  have hσV := h.comm_t_mem (h.U₁_le hw)
  have hw2 := h.sq_mem_V hw
  have hcw : ∀ r ∈ V, r * w = w * r := fun r hr => mem_centralizer_iff.mp (hμV hw) r hr
  have e1 : (w * t) ^ 2 = w ^ 2 * (w * t * w⁻¹ * t⁻¹)⁻¹ := by
    rw [h.sq_mul_t]
    calc w * (t * w * t⁻¹) = w * ((w * t * w⁻¹ * t⁻¹)⁻¹ * w) := by group
      _ = w * (w * (w * t * w⁻¹ * t⁻¹)⁻¹) := by rw [hcw _ (inv_mem hσV)]
      _ = w ^ 2 * (w * t * w⁻¹ * t⁻¹)⁻¹ := by rw [sq]; group
  have e2 : (w ^ 2) ^ 2 = (w * t * w⁻¹ * t⁻¹) ^ 2 := by
    rw [← h.comm_t_of_mem_V hw2, sq w, SzC1.comm_t_mul, ← hcw _ hσV, mul_inv_cancel_right, sq]
  refine h.omega _ (e1 ▸ mul_mem hw2 (inv_mem hσV)) ?_
  rw [e1, (Commute.mul_pow (h.comm _ hw2 _ (inv_mem hσV)) 2), e2, inv_pow, mul_inv_cancel]

theorem exists_nu (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w)
    (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) :
    ∃ ν : K, ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G),
      v ((w * t) ^ 2) = ν * v ((w * t * w⁻¹ * t⁻¹) ^ 2 ^ k) := by
  have hcomm := h.V₁_comm' hK hc hμ hμV hlam
  have hdt : d * t = t * d := (mem_centralizer_singleton_iff.mp h.d_norm.2)
  exact exists_mul_of_hom hμ (M := U₁ ⊓ centralizer (szT₁ L T : Set G))
    (S := fun w => v ((w * t * w⁻¹ * t⁻¹) ^ 2 ^ k)) (φ := fun w => v ((w * t) ^ 2))
    (fun x hx y hy => h.S_mul hK hc (mem_inf.mp hx).1 (mem_inf.mp hy).1)
    (h.S_surj_V₁ hK hc hμ hlam)
    (fun x hx y hy => by
      show v ((x * y * t) ^ 2) = v ((x * t) ^ 2) + v ((y * t) ^ 2)
      have e : (x * y * t) ^ 2 = (x * t) ^ 2 * (y * t) ^ 2 := by
        rw [h.sq_mul_t, h.sq_mul_t, h.sq_mul_t]
        rw [show t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) by group]
        rw [show x * y * ((t * x * t⁻¹) * (t * y * t⁻¹)) =
          x * (y * (t * x * t⁻¹)) * (t * y * t⁻¹) by group,
          hcomm y hy _ (h.t_conj_mem_V₁ hx)]
        group
      rw [e, hc.mul _ (h.sq_mul_t_mem_szA₁ hK hc hμV (mem_inf.mp hx).1)
        _ (h.sq_mul_t_mem_szA₁ hK hc hμV (mem_inf.mp hy).1)])
    (fun w hw h0 => by
      show v ((w * t) ^ 2) = 0
      have hwV := h.mem_V_of_mem_V₁_of_mem_sup hw
        (h.mem_sup_of_S_eq_zero hK hc (mem_inf.mp hw).1 h0)
      rw [h.sq_mul_t, h.inv w hwV, mul_inv_cancel, hc.v_one])
    (fun w hw => ⟨d⁻¹ * w * d, h.conj_d_mem_V₁ hw, h.S_conj_d hK hc (mem_inf.mp hw).1, by
      show v ((d⁻¹ * w * d * t) ^ 2) = _
      have e : (d⁻¹ * w * d * t) ^ 2 = d⁻¹ * (w * t) ^ 2 * d := by
        have e1 : d⁻¹ * w * d * t = d⁻¹ * (w * t) * d := by
          rw [show d⁻¹ * (w * t) * d = d⁻¹ * w * (t * d) by group, ← hdt]; group
        rw [e1, show d⁻¹ * (w * t) * d = d⁻¹ * (w * t) * d⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv]
      rw [e, hc.conj _ (h.sq_mul_t_mem_szA₁ hK hc hμV (mem_inf.mp hw).1)]⟩)

theorem mem_V_of_sq_eq_one (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w)
    (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∃ w₀ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w₀ * t) ^ 2 ≠ 1) {w : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) (h1 : (w * t) ^ 2 = 1) : w ∈ V := by
  obtain ⟨ν, hν'⟩ := h.exists_nu hK hc hμ hμV hlam
  obtain ⟨w₀, hw₀, hw₀1⟩ := hν
  have hν0 : ν ≠ 0 := by
    rintro rfl
    have e := hν' w₀ hw₀
    rw [zero_mul] at e
    exact hw₀1 (hc.eq_one_of_v_eq_zero (h.sq_mul_t_mem_szA₁ hK hc hμV (mem_inf.mp hw₀).1) e)
  have e := hν' w hw
  rw [h1, hc.v_one] at e
  have hS : v ((w * t * w⁻¹ * t⁻¹) ^ 2 ^ k) = 0 :=
    (mul_eq_zero.mp e.symm).resolve_left hν0
  exact h.mem_V_of_mem_V₁_of_mem_sup hw (h.mem_sup_of_S_eq_zero hK hc (mem_inf.mp hw).1 hS)

end Coords

theorem V₁_comm (h : U3C1OuterStage G L f t T d V U U₁ k)
    (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) :
    ∀ x ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), ∀ y ∈ U₁ ⊓ centralizer (szT₁ L T : Set G),
      x * y = y * x := by
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := h.coords
  exact h.V₁_comm' hK hc hμ hμV hlam

theorem sq_sq_eq (h : U3C1OuterStage G L f t T d V U U₁ k)
    (hμV : U₁ ≤ centralizer (V : Set G)) {w : G} (hw : w ∈ U₁) :
    (w ^ 2) ^ 2 = (w * t * w⁻¹ * t⁻¹) ^ 2 := by
  have hσV := h.comm_t_mem (h.U₁_le hw)
  rw [← h.comm_t_of_mem_V (h.sq_mem_V hw), sq w, SzC1.comm_t_mul,
    ← mem_centralizer_iff.mp (hμV hw) _ hσV, mul_inv_cancel_right, sq]

theorem card_V₁ (h : U3C1OuterStage G L f t T d V U U₁ k)
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) :
    Nat.card (U₁ ⊓ centralizer (szT₁ L T : Set G) : Subgroup G) = (2 ^ f) ^ (k + 2) := by
  set V₁ := U₁ ⊓ centralizer (szT₁ L T : Set G) with hV₁
  have hrel1 : (szT₁ L T ⊔ V).relIndex U₁ = 2 ^ f := by
    have h1 := relIndex_mul_card (H := szT₁ L T ⊔ V) (K := U₁)
    rw [inf_of_le_left h.sup_le_U₁, h.card_sup, h.card_U₁] at h1
    have h2 : 2 ^ f * (2 ^ f) ^ (k + 3) = (2 ^ f) ^ (k + 4) := by ring
    exact Nat.eq_of_mul_eq_mul_right (by positivity) (h1.trans h2.symm)
  have hsup : V₁ ⊔ (szT₁ L T ⊔ V) = U₁ := le_antisymm
    (sup_le inf_le_left h.sup_le_U₁)
    (by
      conv_lhs => rw [hlam]
      exact sup_le (le_sup_left.trans le_sup_right) le_sup_left)
  have hinf : V₁ ⊓ (szT₁ L T ⊔ V) = V := le_antisymm
    (fun w hw => h.mem_V_of_mem_V₁_of_mem_sup (mem_inf.mp hw).1 (mem_inf.mp hw).2)
    (le_inf h.V_le_V₁ le_sup_right)
  have hrel2 := SzC1.relIndex_sup_eq_relIndex_inf (H := V₁) (K := szT₁ L T ⊔ V)
    ((inf_le_left.trans h.U₁_le).trans h.U_le_normalizer_sup)
  rw [hsup, hrel1, hinf] at hrel2
  have h3 := relIndex_mul_card (H := V) (K := V₁)
  rw [← hrel2, inf_of_le_left h.V_le_V₁, h.card] at h3
  rw [← h3]
  ring

theorem omega_V₁ (h : U3C1OuterStage G L f t T d V U U₁ k)
    (hμV : U₁ ≤ centralizer (V : Set G)) {w : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) (hw2 : w ^ 2 = 1) :
    w ∈ szA₁ (szT₁ L T) := by
  obtain ⟨K, _, _, _, v, μ, hK, hc, -⟩ := h.coords
  have hk := h.one_le
  have hσ2 : (w * t * w⁻¹ * t⁻¹) ^ 2 = 1 := by
    rw [← h.sq_sq_eq hμV (mem_inf.mp hw).1, hw2, one_pow]
  have hS : v ((w * t * w⁻¹ * t⁻¹) ^ 2 ^ k) = 0 := by
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hj, pow_succ', pow_mul, hσ2, one_pow, hc.v_one]
  exact h.omega w (h.mem_V_of_mem_V₁_of_mem_sup hw
    (h.mem_sup_of_S_eq_zero hK hc (mem_inf.mp hw).1 hS)) hw2

end U3C1OuterStage
end CFSG.SeitzReduction.RankOne
