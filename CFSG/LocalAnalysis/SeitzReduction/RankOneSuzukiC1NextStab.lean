module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1NextFam

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace SzC1

theorem two_transitive_of_transitive {N : Type*} [Group N] {K : Type*} [Field K]
    (φ : N →* Equiv.Perm K) {μ : K} (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) {δ : N}
    (hδ : ∀ c, φ δ c = μ * c) (htr : ∀ c, ∃ n, φ n 0 = c) :
    ∀ a₁ b₁ c₁ e₁ : K, a₁ ≠ b₁ → c₁ ≠ e₁ → ∃ x ∈ φ.range, x a₁ = c₁ ∧ x b₁ = e₁ := by
  intro a₁ b₁ c₁ e₁ hab hce
  obtain ⟨n₁, hn₁⟩ := htr a₁
  obtain ⟨n₂, hn₂⟩ := htr c₁
  set β := φ n₁⁻¹ b₁ with hβ
  set γ := φ n₂⁻¹ e₁ with hγ
  have hinv : ∀ (n : N) (z : K), φ n⁻¹ (φ n z) = z := fun n z => by
    rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Equiv.Perm.one_apply]
  have hinv' : ∀ (n : N) (z : K), φ n (φ n⁻¹ z) = z := fun n z => by
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]
  have hβ0 : β ≠ 0 := by
    intro h0
    apply hab
    rw [← hn₁, ← h0, hβ, hinv']
  have hγ0 : γ ≠ 0 := by
    intro h0
    apply hce
    rw [← hn₂, ← h0, hγ, hinv']
  obtain ⟨j, hj⟩ := hμ (γ / β) (div_ne_zero hγ0 hβ0)
  have hpow : ∀ (i : ℕ) (z : K), φ (δ ^ i) z = μ ^ i * z := by
    intro i
    induction i with
    | zero => intro z; simp
    | succ i ih =>
      intro z
      rw [pow_succ', map_mul, Equiv.Perm.mul_apply, ih, hδ, pow_succ']
      ring
  refine ⟨φ (n₂ * δ ^ j * n₁⁻¹), ⟨_, rfl⟩, ?_, ?_⟩
  · rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hn₁, hinv, hpow,
      mul_zero, hn₂]
  · rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hβ, hpow, hj,
      div_mul_cancel₀ γ hβ0, hγ, hinv']

end SzC1

namespace SzC1Next

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f a : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {u v : G → K} {κ : K} (H : SzC1Next G L f a t T d V U U₁ k K u v κ)
include H

theorem exists_perm_eq
    (hU : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U) (c : K) :
    ∃ n : normalizer (U : Set G), H.perm n 0 = c := by
  by_cases hc0 : c = 0
  · exact ⟨1, by rw [map_one, Equiv.Perm.one_apply, hc0]⟩
  obtain ⟨g, hgN, hgU, P, hP2, hUP, hgP⟩ :=
    exists_normalizer_not_mem_of_not_isSylow H.stage.isPGroup_U hU
  set c₀ := H.perm ⟨g, hgN⟩ 0 with hc₀
  have hc₀0 : c₀ ≠ 0 := by
    intro h0
    rw [hc₀, H.perm_zero] at h0
    have hV := H.stage.mem_V_of_X_eq_zero H.card_K H.coords H.nu (H.comm_t_mem_V₁ hgN) h0
    exact hgU (H.stage.mem_U_of_comm_t_mem hP2 hUP hgP hV)
  obtain ⟨m, hm⟩ := H.gen_mu (c / c₀) (div_ne_zero hc0 hc₀0)
  set δ : normalizer (U : Set G) := ⟨d⁻¹, inv_mem H.stage.d_mem_normalizer_U⟩ with hδ
  have key : ∀ j : ℕ, H.perm (δ ^ j * ⟨g, hgN⟩) 0 = (κ ^ (2 ^ (a + 1) + 1)) ^ j * c₀ := by
    intro j
    induction j with
    | zero => simp [hc₀]
    | succ j ih =>
      rw [pow_succ', mul_assoc, map_mul, Equiv.Perm.mul_apply, ih, H.perm_d_inv]
      ring
  exact ⟨δ ^ m * ⟨g, hgN⟩, by rw [key, hm, div_mul_cancel₀ c hc₀0]⟩

theorem perm_two_transitive
    (hU : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U) :
    ∀ a₁ b₁ c₁ e₁ : K, a₁ ≠ b₁ → c₁ ≠ e₁ → ∃ x ∈ H.perm.range, x a₁ = c₁ ∧ x b₁ = e₁ :=
  SzC1.two_transitive_of_transitive H.perm H.gen_mu (δ := ⟨d⁻¹, inv_mem H.stage.d_mem_normalizer_U⟩)
    H.perm_d_inv (H.exists_perm_eq hU)

theorem mem_U₁_mul_centralizer
    (n : normalizer (U : Set G)) (h0 : H.perm n 0 = 0) :
    ∃ x ∈ U₁, x⁻¹ * (n : G) ∈ centralizer ({t} : Set G) := by
  rw [H.perm_zero] at h0
  have hcV : (n : G) * t * (n : G)⁻¹ * t⁻¹ ∈ V :=
    H.stage.mem_V_of_X_eq_zero H.card_K H.coords H.nu (H.comm_t_mem_V₁ n.2) h0
  obtain ⟨x, hx, hxσ⟩ := H.stage.exists_comm_t_eq H.card_K H.coords H.gen hcV
  refine ⟨x, hx, mem_centralizer_singleton_iff.mpr ?_⟩
  have e : x * t * x⁻¹ = (n : G) * t * (n : G)⁻¹ := by
    calc x * t * x⁻¹ = (x * t * x⁻¹ * t⁻¹) * t := by group
      _ = ((n : G) * t * (n : G)⁻¹ * t⁻¹) * t := by rw [hxσ]
      _ = (n : G) * t * (n : G)⁻¹ := by group
  calc x⁻¹ * (n : G) * t = x⁻¹ * ((n : G) * t * (n : G)⁻¹) * (n : G) := by group
    _ = x⁻¹ * (x * t * x⁻¹) * (n : G) := by rw [e]
    _ = t * (x⁻¹ * (n : G)) := by group

theorem perm_zero_of_mem_centralizer
    (n : normalizer (U : Set G)) (hn : (n : G) ∈ centralizer ({t} : Set G)) :
    H.perm n 0 = 0 := by
  rw [H.perm_zero, mem_centralizer_singleton_iff.mp hn, mul_inv_cancel_right, mul_inv_cancel,
    one_pow, H.coords.v_one]


theorem odd_mul : Odd ((2 ^ f - 1) * f) := by
  have hf := H.stage.hfa
  refine Nat.odd_mul.mpr ⟨⟨2 ^ (2 * a) - 1, ?_⟩, ⟨a, by omega⟩⟩
  have h1 : 1 ≤ 2 ^ (2 * a) := Nat.one_le_two_pow
  rw [hf, pow_succ]
  omega

theorem perm_stabilizer :
    Odd (Nat.card (H.perm.range ⊓ MulAction.stabilizer (Equiv.Perm K) (0 : K) :
      Subgroup (Equiv.Perm K))) ∧
    Nat.card (H.perm.range ⊓ MulAction.stabilizer (Equiv.Perm K) (0 : K) :
      Subgroup (Equiv.Perm K)) ∣ (2 ^ f - 1) * f := by
  set M : Subgroup G := normalizer (U : Set G) ⊓ centralizer ({t} : Set G) with hM
  have hMN : M ≤ normalizer (U : Set G) := inf_le_left
  set ψ : M →* Equiv.Perm K := H.perm.comp (Subgroup.inclusion hMN) with hψ
  have hrange : H.perm.range ⊓ MulAction.stabilizer (Equiv.Perm K) (0 : K) = ψ.range := by
    ext p
    constructor
    · rintro ⟨⟨n, rfl⟩, hn0⟩
      have h0 : H.perm n 0 = 0 := MulAction.mem_stabilizer_iff.mp hn0
      obtain ⟨x, hx, hxn⟩ := H.mem_U₁_mul_centralizer n h0
      have hxN : x ∈ normalizer (U : Set G) := le_normalizer (H.stage.U₁_le hx)
      have hm : x⁻¹ * (n : G) ∈ M := mem_inf.mpr ⟨mul_mem (inv_mem hxN) n.2, hxn⟩
      refine ⟨⟨_, hm⟩, ?_⟩
      have e : Subgroup.inclusion hMN ⟨_, hm⟩ = (⟨x, hxN⟩ : normalizer (U : Set G))⁻¹ * n :=
        Subtype.ext rfl
      rw [hψ, MonoidHom.comp_apply, e, map_mul, map_inv,
        H.perm_eq_one_of_mem_U ⟨x, hxN⟩ (H.stage.U₁_le hx), inv_one, one_mul]
    · rintro ⟨m, rfl⟩
      refine ⟨⟨_, rfl⟩, MulAction.mem_stabilizer_iff.mpr ?_⟩
      exact H.perm_zero_of_mem_centralizer _ (mem_inf.mp m.2).2
  have hTU : T ≤ U := by
    rw [H.stage.start.facts.1]
    exact sup_le (H.stage.T₁_le_U₁.trans H.stage.U₁_le) (zpowers_le.mpr H.stage.t_mem_U)
  have hTM : T ≤ M := le_inf (hTU.trans le_normalizer) H.stage.start.le
  have hcard := SzC1.card_eq_card_ker_mul_card_range ψ
  have hTker : T.subgroupOf M ≤ ψ.ker := fun x hx => by
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply]
    exact H.perm_eq_one_of_mem_U _ (hTU (mem_subgroupOf.mp hx))
  have hTdvd : Nat.card T ∣ Nat.card ψ.ker := by
    have := Subgroup.card_dvd_of_le hTker
    rwa [Nat.card_congr (subgroupOfEquivOfLe hTM).toEquiv] at this
  have hMdvd : Nat.card M ∣ 2 * (2 ^ f) ^ 2 * ((2 ^ f - 1) * f) :=
    (Subgroup.card_dvd_of_le (le_inf (hMN.trans (H.stage.normalizer_U_le_normalizer_T₁ H.card_K
      H.coords H.mu H.lam H.nu)) inf_le_right)).trans
      H.stage.start.card_normalizer_szT₁_inf_centralizer_dvd
  have hTcard : Nat.card T = 2 * 2 ^ f * 2 ^ f := H.stage.start.facts.2.2.1
  obtain ⟨j, hj⟩ := hTdvd
  have hdvd : Nat.card ψ.range ∣ (2 ^ f - 1) * f := by
    have h1 : Nat.card T * (j * Nat.card ψ.range) ∣ Nat.card T * ((2 ^ f - 1) * f) := by
      rw [← mul_assoc, ← hj, ← hcard, hTcard]
      rw [show 2 * 2 ^ f * 2 ^ f * ((2 ^ f - 1) * f) = 2 * (2 ^ f) ^ 2 * ((2 ^ f - 1) * f) by ring]
      exact hMdvd
    have h2 := Nat.dvd_of_mul_dvd_mul_left Nat.card_pos h1
    exact (Dvd.intro_left _ rfl).trans h2
  rw [hrange]
  exact ⟨Odd.of_dvd_nat H.odd_mul hdvd, hdvd⟩

end SzC1Next

end CFSG.SeitzReduction.RankOne
