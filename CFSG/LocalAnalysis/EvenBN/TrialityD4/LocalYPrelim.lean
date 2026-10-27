module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalVPrelim

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup
open scoped commutatorElement Matrix

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem φ_pow_mem_Y (k : ℕ) {y : X} (hy : y ∈ d.Y) : (d.φ ^ k) y ∈ d.Y := by
  have h5 := map_rangeSubgroup_le_D4 d.x₅_add (d.φ ^ k) _ (d.φ_pow_x₅ k)
  have h6 := map_rangeSubgroup_le_D4 d.x₆_add (d.φ ^ k) _ (d.φ_pow_x₆ k)
  have hY : d.Y.map (d.φ ^ k).toMonoidHom ≤ d.Y := by
    simp only [Y, V, Subgroup.map_sup, U₅, U₆]
    exact sup_le_sup h5 h6
  exact hY ⟨y, hy, rfl⟩

theorem φ_pow_mem_M (k : ℕ) {y : X} (hy : y ∈ d.M) : (d.φ ^ k) y ∈ d.M := by
  have h1 := map_rangeSubgroup_le_D4 d.x₁_add (d.φ ^ k) _ (d.φ_pow_x₁ k)
  have h3 := map_rangeSubgroup_le_D4 d.x₃_add (d.φ ^ k) _ (d.φ_pow_x₃ k)
  have h4 := map_rangeSubgroup_le_D4 d.x₄_add (d.φ ^ k) _ (d.φ_pow_x₄ k)
  have h5 := map_rangeSubgroup_le_D4 d.x₅_add (d.φ ^ k) _ (d.φ_pow_x₅ k)
  have h6 := map_rangeSubgroup_le_D4 d.x₆_add (d.φ ^ k) _ (d.φ_pow_x₆ k)
  have hM : d.M.map (d.φ ^ k).toMonoidHom ≤ d.M := by
    simp only [M, F, W, Y, V, Subgroup.map_sup, U₁, U₃, U₄, U₅, U₆]
    exact sup_le_sup h1 (sup_le_sup h3 (sup_le_sup h4 (sup_le_sup h5 h6)))
  exact hM ⟨y, hy, rfl⟩

theorem φ_pow_mem_leviLong (k : ℕ) {y : X} (hy : y ∈ d.leviLong) :
    (d.φ ^ k) y ∈ d.leviLong := by
  have h : d.leviLong.map (d.φ ^ k).toMonoidHom ≤ d.leviLong := by
    rw [leviLong, MonoidHom.map_closure, closure_le]
    rintro _ ⟨z, hz | hz, rfl⟩
    · obtain ⟨a, rfl⟩ := hz
      change (d.φ ^ k) (d.x₂ a) ∈ d.leviLong
      rw [d.φ_pow_x₂]
      exact d.x₂_mem_leviLong _
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      change (d.φ ^ k) d.v ∈ d.leviLong
      rw [d.φ_pow_v]
      exact d.v_mem_leviLong
  exact h ⟨y, hy, rfl⟩

theorem φ_pow_apply_of_mem_leviLong {k : ℕ} (hk : ∀ c : d.Γ₀, c ^ 2 ^ k = c) {y : X}
    (hy : y ∈ d.leviLong) : (d.φ ^ k) y = y := by
  have h : d.leviLong ≤ (d.φ ^ k).toMonoidHom.eqLocus (MonoidHom.id X) := by
    rw [leviLong, closure_le]
    rintro _ (⟨a, rfl⟩ | hz)
    · change (d.φ ^ k) (d.x₂ a) = d.x₂ a
      rw [d.φ_pow_x₂, hk]
    · rw [Set.mem_singleton_iff.1 hz]
      exact d.φ_pow_v k
  exact h hy

theorem leviLong_le_normalizer_M : d.leviLong ≤ normalizer (d.M : Set X) := by
  rw [← d.normalizer_Y_eq_normalizer_W_and_M.2]
  exact d.leviLong_le_normalizer_Y

theorem J₂_le_normalizer_M : d.J₂ ≤ normalizer (d.M : Set X) :=
  inf_le_left.trans d.J_le_normalizer_M

theorem exists_mul_of_mem_normalizer_Y {g : X} (hg : g ∈ normalizer (d.Y : Set X)) :
    ∃ m ∈ d.M, ∃ s ∈ d.leviLong, ∃ j ∈ d.J₂, g = m * s * j := by
  obtain ⟨-, -, h2, -, hJ, -⟩ := d.yamada_three_eight_five
  rw [h2] at hg
  have h1 : d.leviLong ⊔ d.J₂ ≤ normalizer (d.M : Set X) :=
    sup_le d.leviLong_le_normalizer_M d.J₂_le_normalizer_M
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ h1, Set.mem_mul] at hg
  obtain ⟨m, hm, b, hb, rfl⟩ := hg
  have h3 : d.J₂ ≤ normalizer (d.leviLong : Set X) :=
    hJ.trans (centralizer_le_normalizer _)
  rw [SetLike.mem_coe, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ h3,
    Set.mem_mul] at hb
  obtain ⟨s, hs, j, hj, rfl⟩ := hb
  exact ⟨m, hm, s, hs, j, hj, by rw [mul_assoc]⟩

theorem M_inf_leviLong : d.M ⊓ d.leviLong = ⊥ :=
  le_bot_iff.1 ((inf_le_inf_left _ le_sup_left).trans d.yamada_three_eight_five.2.2.2.2.2.le)

theorem M_inf_J₂ : d.M ⊓ d.J₂ = ⊥ :=
  le_bot_iff.1 ((inf_le_inf_left _ le_sup_right).trans d.yamada_three_eight_five.2.2.2.2.2.le)

theorem yv_mem_Y (w : Fin 2 → d.Γ₀) : d.yv w ∈ d.Y :=
  mul_mem (d.x₅_mem_Y _) (d.x₆_mem_Y _)

theorem M_le_centralizer_Y : d.M ≤ centralizer (d.Y : Set X) := by
  intro m hm
  rw [mem_centralizer_iff]
  intro y hy
  have h := commutator_mem_commutator hm hy
  rw [d.commutator_M_Y, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
  exact h.symm

theorem mem_M_of_mem_S_of_conj_v_mem_S {g : X} (hg : g ∈ d.S) (hv : d.v * g * d.v ∈ d.S) :
    g ∈ d.M := by
  obtain ⟨a, n, hn, rfl⟩ := d.mem_S_iff_x₂.1 hg
  have hvn : d.v * n * d.v ∈ d.M := by
    have := (mem_normalizer_iff.1 d.v_mem_normalizer_M n).1 hn
    rwa [d.v_inv] at this
  have h1 : d.v * d.x₂ a * d.v ∈ d.S := by
    have e : d.v * (d.x₂ a * n) * d.v * (d.v * n * d.v)⁻¹ = d.v * d.x₂ a * d.v⁻¹ := by group
    rw [d.v_inv] at e
    rw [← e]
    exact mul_mem hv (inv_mem (d.M_le_S hvn))
  have ha : a = 0 := by
    by_contra ha
    exact d.v_x₂_v_not_mem_B ha (d.S_le_B h1)
  rw [ha, d.x₂_zero, one_mul]
  exact hn

theorem le_M_of_isPGroup {Q : Subgroup X} (hQ : IsPGroup 2 Q)
    (hS : d.S ≤ normalizer (Q : Set X)) (hv : d.v ∈ normalizer (Q : Set X)) : Q ≤ d.M := by
  have := d.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := d.exists_sylow_eq_S
  have hQS : Q ≤ d.S := by
    have h1 : IsPGroup 2 (Q ⊔ (P : Subgroup X) : Subgroup X) :=
      hQ.to_sup_of_normal_left' P.isPGroup' (hP ▸ hS)
    have h2 := P.is_maximal' h1 le_sup_right
    rw [← hP, ← h2]
    exact le_sup_left
  intro x hx
  have hvx : d.v * x * d.v ∈ d.S := by
    have := (mem_normalizer_iff.1 hv x).1 hx
    rw [d.v_inv] at this
    exact hQS this
  exact d.mem_M_of_mem_S_of_conj_v_mem_S (hQS hx) hvx

theorem mem_normalizer_Y_of_conj_mul_φ_pow {g : X} {k : ℕ}
    (hY : ∀ y ∈ d.Y, (MulAut.conj g * d.φ ^ k) y ∈ d.Y) : g ∈ normalizer (d.Y : Set X) := by
  have := d.finite
  refine mem_normalizer_fintype fun y hy => ?_
  have hy' : y ∈ Set.range d.yv := by rw [d.range_yv]; exact hy
  obtain ⟨w, rfl⟩ := hy'
  obtain ⟨c₀, hc₀⟩ := d.pow_two_pow_surjective_Γ₀ k (w 0)
  obtain ⟨c₁, hc₁⟩ := d.pow_two_pow_surjective_Γ₀ k (w 1)
  have h := hY (d.x₅ c₀ * d.x₆ c₁) (mul_mem (d.x₅_mem_Y c₀) (d.x₆_mem_Y c₁))
  rwa [MulAut.mul_apply, map_mul, d.φ_pow_x₅, d.φ_pow_x₆, hc₀, hc₁, MulAut.conj_apply] at h

theorem eq_conj_of_trivial_mod_M {α : MulAut X} (hY : ∀ y ∈ d.Y, α y ∈ d.Y)
    (hα : ∀ y ∈ d.leviLong, α y * y⁻¹ ∈ d.M) (hJ : ∀ y ∈ d.J₂, α y * y⁻¹ ∈ d.M) :
    ∃ m ∈ d.M, ∃ j ∈ d.J₂, α = MulAut.conj (m * j) := by
  obtain ⟨g, k, rfl⟩ := d.aut_eq α
  obtain ⟨m, hm, s, hs, j, hj, rfl⟩ :=
    d.exists_mul_of_mem_normalizer_Y (d.mem_normalizer_Y_of_conj_mul_φ_pow hY)
  have hjc : ∀ z ∈ d.leviLong, j * z * j⁻¹ = z := fun z hz => by
    rw [← mem_centralizer_iff.1 (d.yamada_three_eight_five.2.2.2.2.1 hj) z hz,
      mul_inv_cancel_right]
  have hfix : ∀ y ∈ d.leviLong, s * (d.φ ^ k) y * s⁻¹ = y := by
    intro y hy
    have hφy := d.φ_pow_mem_leviLong k hy
    have hz : s * (d.φ ^ k) y * s⁻¹ ∈ d.leviLong := mul_mem (mul_mem hs hφy) (inv_mem hs)
    have h1 := hα y hy
    rw [MulAut.mul_apply, MulAut.conj_apply,
      show m * s * j * (d.φ ^ k) y * (m * s * j)⁻¹ =
        m * (s * (j * (d.φ ^ k) y * j⁻¹) * s⁻¹) * m⁻¹ by group, hjc _ hφy] at h1
    set z := s * (d.φ ^ k) y * s⁻¹
    have hzm : z * m⁻¹ * z⁻¹ ∈ d.M :=
      (mem_normalizer_iff.1 (d.leviLong_le_normalizer_M hz) _).1 (inv_mem hm)
    have h2 : z * y⁻¹ ∈ d.M := by
      have e : z * y⁻¹ = (z * m⁻¹ * z⁻¹)⁻¹ * m⁻¹ * (m * z * m⁻¹ * y⁻¹) := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hzm) (inv_mem hm)) h1
    have h3 : z * y⁻¹ ∈ d.M ⊓ d.leviLong := Subgroup.mem_inf.2 ⟨h2, mul_mem hz (inv_mem hy)⟩
    rw [d.M_inf_leviLong, mem_bot, mul_inv_eq_one] at h3
    exact h3
  have h1 := hfix (d.x₂ 1) (d.x₂_mem_leviLong 1)
  rw [d.φ_pow_x₂, one_pow] at h1
  have hU₂c : ∀ a b : d.Γ₀, d.x₂ a * d.x₂ b = d.x₂ b * d.x₂ a := fun a b =>
    commute_of_add d.x₂_add a b
  obtain ⟨x, hx, h, hh, rfl⟩ : ∃ x ∈ d.U₂, ∃ h ∈ d.J₄, s = x * h := by
    rcases d.mem_leviLong_iff.1 hs with hB | ⟨x, hx, h, hh, y, hy, rfl⟩
    · exact hB
    exfalso
    obtain ⟨b, rfl⟩ := hy
    have e : d.v * d.x₂ 1 * d.v = (x * h)⁻¹ * d.x₂ 1 * (x * h) := by
      have e1 : x * h * d.v * d.x₂ b * d.x₂ 1 * (x * h * d.v * d.x₂ b)⁻¹ =
          x * h * (d.v * d.x₂ 1 * d.v⁻¹) * (x * h)⁻¹ := by
        rw [show x * h * d.v * d.x₂ b * d.x₂ 1 * (x * h * d.v * d.x₂ b)⁻¹ =
          x * h * d.v * (d.x₂ b * d.x₂ 1 * (d.x₂ b)⁻¹) * d.v⁻¹ * (x * h)⁻¹ by group,
          hU₂c b 1, mul_inv_cancel_right]
        group
      rw [e1, d.v_inv] at h1
      calc d.v * d.x₂ 1 * d.v = (x * h)⁻¹ * (x * h * (d.v * d.x₂ 1 * d.v) * (x * h)⁻¹) *
            (x * h) := by group
        _ = (x * h)⁻¹ * d.x₂ 1 * (x * h) := by rw [h1]
    have hxh : x * h ∈ d.B := mul_mem (d.S_le_B (d.U₂_le_S hx)) (d.J_le_B hh.1)
    refine d.v_x₂_v_not_mem_B one_ne_zero ?_
    rw [e]
    exact mul_mem (mul_mem (inv_mem hxh) (d.S_le_B (d.U₂_le_S (d.x₂_mem_U₂ 1)))) hxh
  rw [d.J₄_eq_range_hA] at hh
  obtain ⟨β, rfl⟩ := hh
  obtain ⟨b, rfl⟩ := hx
  have hcoord : ∀ a : d.Γ₀, ((β ^ 2 : (d.Γ₀)ˣ) : d.Γ₀) * a ^ 2 ^ k = a := by
    intro a
    have h2 := hfix (d.x₂ a) (d.x₂_mem_leviLong a)
    rw [d.φ_pow_x₂, show d.x₂ b * d.hA β * d.x₂ (a ^ 2 ^ k) * (d.x₂ b * d.hA β)⁻¹ =
        d.x₂ b * (d.hA β * d.x₂ (a ^ 2 ^ k) * (d.hA β)⁻¹) * (d.x₂ b)⁻¹ by group,
      d.hA_apply, d.torus_x₂, hU₂c b, mul_inv_cancel_right] at h2
    exact d.x₂_injective h2
  have hβ : β = 1 := d.units₀_eq_one_of_sq (Units.ext (by simpa using hcoord 1))
  subst hβ
  rw [map_one, mul_one] at hfix hJ ⊢
  have hb : b = 0 := by
    by_contra hb
    have h2 := hfix d.v d.v_mem_leviLong
    rw [d.φ_pow_v] at h2
    refine d.v_x₂_v_not_mem_B hb ?_
    have e : d.v * d.x₂ b * d.v = d.x₂ b := by
      calc d.v * d.x₂ b * d.v = d.v * (d.x₂ b * d.v * (d.x₂ b)⁻¹) * d.x₂ b := by group
        _ = d.x₂ b := by rw [h2, d.v_mul_self, one_mul]
    rw [e]
    exact d.S_le_B (d.U₂_le_S (d.x₂_mem_U₂ b))
  simp only [hb, d.x₂_zero, mul_one, one_mul, inv_one] at hfix hJ ⊢
  have hφ : d.φ ^ k = 1 := by
    refine d.φ_pow_eq_one_of_forall fun c => ?_
    by_cases hc : c = 0
    · rw [hc, zero_pow (pow_ne_zero _ two_ne_zero)]
    set μ : d.Γˣ := Units.mk0 c hc
    have hjμ : d.torus (1, μ) ∈ d.J₂ := (d.torus_mem_J₂_iff _).2 rfl
    have h2 := hJ _ hjμ
    rw [MulAut.mul_apply, MulAut.conj_apply, d.φ_pow_torus,
      show m * j * d.torus ((1, μ) ^ 2 ^ k) * (m * j)⁻¹ * (d.torus (1, μ))⁻¹ =
        m * (j * d.torus ((1, μ) ^ 2 ^ k) * j⁻¹) * m⁻¹ * (d.torus (1, μ))⁻¹ by group,
      show j * d.torus ((1, μ) ^ 2 ^ k) * j⁻¹ = d.torus ((1, μ) ^ 2 ^ k) by
        rw [d.J_commute hj.1 (d.torus_mem_J _), mul_inv_cancel_right]] at h2
    have h3 : d.torus ((1, μ) ^ 2 ^ k) * (d.torus (1, μ))⁻¹ ∈ d.M := by
      have hmT : m * d.torus ((1, μ) ^ 2 ^ k) * m⁻¹ * (d.torus ((1, μ) ^ 2 ^ k))⁻¹ ∈ d.M := by
        rw [show m * d.torus ((1, μ) ^ 2 ^ k) * m⁻¹ * (d.torus ((1, μ) ^ 2 ^ k))⁻¹ =
          m * (d.torus ((1, μ) ^ 2 ^ k) * m⁻¹ * (d.torus ((1, μ) ^ 2 ^ k))⁻¹) by group]
        exact mul_mem hm ((mem_normalizer_iff.1 (d.J_le_normalizer_M (d.torus_mem_J _)) _).1
          (inv_mem hm))
      have e : d.torus ((1, μ) ^ 2 ^ k) * (d.torus (1, μ))⁻¹ =
          (m * d.torus ((1, μ) ^ 2 ^ k) * m⁻¹ * (d.torus ((1, μ) ^ 2 ^ k))⁻¹)⁻¹ *
            (m * d.torus ((1, μ) ^ 2 ^ k) * m⁻¹ * (d.torus (1, μ))⁻¹) := by group
      rw [e]
      exact mul_mem (inv_mem hmT) h2
    have h4 : d.torus ((1, μ) ^ 2 ^ k) * (d.torus (1, μ))⁻¹ ∈ d.S ⊓ d.J :=
      Subgroup.mem_inf.2 ⟨d.M_le_S h3, mul_mem (d.torus_mem_J _) (inv_mem (d.torus_mem_J _))⟩
    rw [d.S_inf_J, mem_bot, mul_inv_eq_one] at h4
    have h5 := congrArg (fun p : (d.Γ₀)ˣ × d.Γˣ => ((p.2 : d.Γˣ) : d.Γ)) (d.torus_injective h4)
    simpa [μ] using h5
  rw [hφ, mul_one]
  exact ⟨m, hm, j, hj, rfl⟩

theorem eq_one_of_mul_pow_eq_one_M {m j : X} (hm : m ∈ d.M) (hj : j ∈ d.J₂) {a : ℕ}
    (h : (m * j) ^ 2 ^ a = 1) : j = 1 := by
  have hpow : ∀ e : ℕ, ∃ m' ∈ d.M, (m * j) ^ e = m' * j ^ e := by
    intro e
    induction e with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ e ih =>
      obtain ⟨m', hm', he⟩ := ih
      have hjM : j ^ e ∈ normalizer (d.M : Set X) := pow_mem (d.J₂_le_normalizer_M hj) e
      refine ⟨m' * (j ^ e * m * (j ^ e)⁻¹), mul_mem hm' ((mem_normalizer_iff.1 hjM m).1 hm), ?_⟩
      rw [pow_succ, he, pow_succ]
      group
  obtain ⟨m', hm', he⟩ := hpow (2 ^ a)
  rw [h] at he
  have hjM : j ^ 2 ^ a ∈ d.M ⊓ d.J₂ := by
    refine Subgroup.mem_inf.2 ⟨?_, pow_mem hj _⟩
    rw [eq_inv_of_mul_eq_one_right he.symm]
    exact inv_mem hm'
  rw [d.M_inf_J₂, mem_bot] at hjM
  obtain ⟨⟨l, μ⟩, rfl, hl⟩ := d.mem_J₂.1 hj
  dsimp only at hl
  subst hl
  rw [← map_pow] at hjM
  have h1 := d.torus_injective (hjM.trans (map_one d.torus).symm)
  have hμ : ((μ : d.Γˣ) : d.Γ) ^ 2 ^ a = 1 ^ 2 ^ a := by
    have := congrArg (fun p => ((p.2 : d.Γˣ) : d.Γ)) h1
    simpa using this
  have hμ' : μ = 1 := Units.ext (d.pow_two_pow_injective a hμ)
  rw [hμ']
  exact map_one d.torus

theorem torus_conj_yv_of_fst_eq_one (μ : d.Γˣ) (w : Fin 2 → d.Γ₀) :
    d.torus (1, μ) * d.yv w * (d.torus (1, μ))⁻¹ = d.yv (d.nm (μ : d.Γ) • w) := by
  simp only [yv, Pi.smul_apply, smul_eq_mul]
  rw [show d.torus (1, μ) * (d.x₅ (w 0) * d.x₆ (w 1)) * (d.torus (1, μ))⁻¹ =
      (d.torus (1, μ) * d.x₅ (w 0) * (d.torus (1, μ))⁻¹) *
        (d.torus (1, μ) * d.x₆ (w 1) * (d.torus (1, μ))⁻¹) by group, d.torus_x₅, d.torus_x₆]
  simp only [Units.val_one, one_mul]

theorem exists_of_centralizes_Y {g : X} {k : ℕ}
    (hY : ∀ y ∈ d.Y, (MulAut.conj g * d.φ ^ k) y = y) :
    ∃ m ∈ d.M, ∃ j ∈ d.J₂, g = m * j ∧ j ∈ centralizer (d.Y : Set X) ∧
      ∀ c : d.Γ₀, c ^ 2 ^ k = c := by
  obtain ⟨m, hm, s, hs, j, hj, rfl⟩ := d.exists_mul_of_mem_normalizer_Y
    (d.mem_normalizer_Y_of_conj_mul_φ_pow fun y hy => (hY y hy).symm ▸ hy)
  obtain ⟨⟨l, μ⟩, rfl, hl⟩ := d.mem_J₂.1 hj
  dsimp only at hl
  subst hl
  set A := (d.leviLongRep ⟨s, hs⟩ : Matrix (Fin 2) (Fin 2) d.Γ₀) with hA
  set ν := d.nm (μ : d.Γ) with hν
  have hact : ∀ w : Fin 2 → d.Γ₀,
      A *ᵥ (ν • fun i => w i ^ 2 ^ k) = w := by
    intro w
    have h1 := hY (d.yv w) (d.yv_mem_Y w)
    rw [MulAut.mul_apply, MulAut.conj_apply] at h1
    have hφ : (d.φ ^ k) (d.yv w) = d.yv fun i => w i ^ 2 ^ k := by
      simp only [yv, map_mul, d.φ_pow_x₅, d.φ_pow_x₆]
    rw [hφ, show m * s * d.torus (1, μ) * d.yv (fun i => w i ^ 2 ^ k) *
        (m * s * d.torus (1, μ))⁻¹ = m * (s * (d.torus (1, μ) * d.yv (fun i => w i ^ 2 ^ k) *
          (d.torus (1, μ))⁻¹) * s⁻¹) * m⁻¹ by group, d.torus_conj_yv_of_fst_eq_one,
      show s = ((⟨s, hs⟩ : d.leviLong) : X) from rfl, d.leviLongRep_spec] at h1
    have hmY : m * d.yv (A *ᵥ (ν • fun i => w i ^ 2 ^ k)) * m⁻¹ =
        d.yv (A *ᵥ (ν • fun i => w i ^ 2 ^ k)) := by
      rw [← mem_centralizer_iff.1 (d.M_le_centralizer_Y hm) _ (d.yv_mem_Y _),
        mul_inv_cancel_right]
    rw [hmY] at h1
    exact d.yv_injective h1
  have hν0 : ν ≠ 0 := by
    rw [hν]
    exact (d.nmUnits μ).ne_zero
  have hv0 : (ν • fun i => (![1, 0] : Fin 2 → d.Γ₀) i ^ 2 ^ k) = ![ν, 0] := by
    ext i
    fin_cases i <;> simp
  have hv1 : (ν • fun i => (![0, 1] : Fin 2 → d.Γ₀) i ^ 2 ^ k) = ![0, ν] := by
    ext i
    fin_cases i <;> simp
  have e0 := hact ![1, 0]
  rw [hv0] at e0
  have e1 := hact ![0, 1]
  rw [hv1] at e1
  have e00 : A 0 0 * ν = 1 := by
    have := congrFun e0 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have e10 : A 1 0 * ν = 0 := by
    have := congrFun e0 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have e01 : A 0 1 * ν = 0 := by
    have := congrFun e1 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have e11 : A 1 1 * ν = 1 := by
    have := congrFun e1 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hA10 : A 1 0 = 0 := (mul_eq_zero.1 e10).resolve_right hν0
  have hA01 : A 0 1 = 0 := (mul_eq_zero.1 e01).resolve_right hν0
  have hdet : A 0 0 * A 1 1 = 1 := by
    have := (d.leviLongRep ⟨s, hs⟩).2
    rw [Matrix.det_fin_two] at this
    rw [← hA] at this
    rw [hA10, hA01, mul_zero, sub_zero] at this
    exact this
  have hν1 : ν = 1 := by
    have h1 : (A 0 0 * ν) * (A 1 1 * ν) = 1 := by rw [e00, e11, one_mul]
    rw [show A 0 0 * ν * (A 1 1 * ν) = (A 0 0 * A 1 1) * (ν * ν) by ring, hdet, one_mul] at h1
    have h2 : (ν + 1) * (ν + 1) = 0 := by
      have h3 : (ν + 1) * (ν + 1) = ν * ν + 1 := by
        rw [show (ν + 1) * (ν + 1) = ν * ν + (ν + ν) + 1 by ring, d.add_self_Γ₀, add_zero]
      rw [h3, h1, d.add_self_Γ₀]
    have h4 := mul_self_eq_zero.1 h2
    rw [← sub_eq_zero, sub_eq_add_neg, show (-1 : d.Γ₀) = 1 by
      rw [neg_eq_iff_add_eq_zero, d.add_self_Γ₀]]
    exact h4
  have hA1 : A = 1 := by
    rw [hν1, mul_one] at e00 e11
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e00, e11, hA10, hA01]
  have hs1 : s = 1 := by
    have h1 : d.leviLongRep ⟨s, hs⟩ = 1 := Subtype.ext hA1
    rw [← map_one d.leviLongRep] at h1
    exact congrArg Subtype.val (d.leviLongRep_bijective.1 h1)
  subst hs1
  refine ⟨m, hm, d.torus (1, μ), hj, by rw [mul_one], ?_, fun c => ?_⟩
  · rw [mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ Set.range d.yv := by rw [d.range_yv]; exact hy
    obtain ⟨w, rfl⟩ := hy'
    have h1 := d.torus_conj_yv_of_fst_eq_one μ w
    rw [← hν, hν1, one_smul] at h1
    calc d.yv w * d.torus (1, μ) = d.torus (1, μ) * d.yv w * (d.torus (1, μ))⁻¹ *
          d.torus (1, μ) := by rw [h1]
      _ = d.torus (1, μ) * d.yv w := by group
  · have h1 := hact ![c, 0]
    rw [hA1, Matrix.one_mulVec, hν1, one_smul] at h1
    simpa using congrFun h1 0

end TrialityD4Data

end CFSG.LocalAnalysis.EvenBN.TrialityD4
