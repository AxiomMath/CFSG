module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1NextLevel

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1Next

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {v : G → K} {μ : K}

section NoU'

variable (H : U3C1Next G L f t T d V U U₁ k K v μ)
include H

theorem U₁_le_centralizer_V₁ :
    U₁ ≤ centralizer ((U₁ ⊓ centralizer (szT₁ L T : Set G) : Subgroup G) : Set G) := by
  intro x hx
  obtain ⟨y, hy, w, hw, rfl⟩ := H.stage.exists_mul_V₁ H.lam hx
  exact mul_mem
    (mem_centralizer_iff.mpr fun z hz => (mem_centralizer_iff.mp (mem_inf.mp hz).2 y hy).symm)
    (mem_centralizer_iff.mpr fun z hz => H.V₁_comm hz hw)

theorem normalizer_U_le_normalizer_U₁ :
    normalizer (U : Set G) ≤ normalizer (U₁ : Set G) := by
  intro n hn
  refine mem_normalizer_iff.mpr fun w => ⟨fun hw => H.stage.conj_mem_U₁_of_normalizer H.mu hn hw,
    fun hw => ?_⟩
  have := H.stage.conj_mem_U₁_of_normalizer H.mu (inv_mem hn) hw
  rwa [show n⁻¹ * (n * w * n⁻¹) * n⁻¹⁻¹ = w by group] at this

theorem inv_eq_self_of_mem_szA₁ {b : G} (hb : b ∈ szA₁ (szT₁ L T)) : b⁻¹ = b :=
  inv_eq_of_mul_eq_one_left (by rw [← sq]; exact H.coords.sq_eq_one hb)

theorem M_eq_X_of_mul_t {z : G} (hzt : z * t ∈ U₁) {w : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    v ((w⁻¹ * (z * w * z⁻¹)) ^ 2 ^ k) = v (w ^ 2 ^ (k + 1)) := by
  have hc := H.U₁_le_centralizer_V₁ hzt
  have e : z * w * z⁻¹ = w⁻¹ := by
    have hz : z = (z * t) * t := by rw [mul_assoc, H.stage.t_mul_self, mul_one]
    rw [hz]
    calc z * t * t * w * (z * t * t)⁻¹ = (z * t) * (t * w * t⁻¹) * (z * t)⁻¹ := by group
      _ = (z * t) * w⁻¹ * (z * t)⁻¹ := by rw [H.stage.inv_V₁ H.nu hw]
      _ = w⁻¹ := by rw [← mem_centralizer_iff.mp hc _ (inv_mem hw)]; group
  rw [e, show w⁻¹ * w⁻¹ = (w ^ 2)⁻¹ by rw [sq, mul_inv_rev], inv_pow, ← pow_mul, ← pow_succ',
    H.inv_eq_self_of_mem_szA₁ (H.stage.pow_mem_szA₁_V₁ hw)]

theorem mem_U₁_of_M_eq_zero {z : G} (hz : z ∈ U)
    (hM : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), v ((w⁻¹ * (z * w * z⁻¹)) ^ 2 ^ k) = 0) :
    z ∈ U₁ := by
  rcases H.stage.mem_or_mul_t_mem hz with h | h
  · exact h
  · exfalso
    have e := H.M_eq_X_of_mul_t h (H.sec_mem 1)
    rw [hM _ (H.sec_mem 1), H.sec_X] at e
    exact zero_ne_one e

theorem mu_ne_one : μ ≠ 1 :=
  ne_one_of_generator (by
    rw [H.card_K]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) H.stage.start.two_le) H.gen

end NoU'

namespace NextUData

variable {H : U3C1Next G L f t T d V U U₁ k K v μ} {U' : Subgroup G} (hD : H.NextUData U')
include hD

theorem M_mul {x y : G} (hx : x ∈ U') (hy : y ∈ U') {w : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    v ((w⁻¹ * (x * y * w * (x * y)⁻¹)) ^ 2 ^ k) =
      v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k) + v ((w⁻¹ * (y * w * y⁻¹)) ^ 2 ^ k) := by
  have hcx := hD.chi_mem_V hx hw
  have hcy := hD.chi_mem_V hy hw
  have hxcy : x * (w⁻¹ * (y * w * y⁻¹)) * x⁻¹ ∈ V :=
    (mem_normalizer_iff.mp (H.stage.normalizer_U_le_normalizer_V (hD.le hx)) _).mp hcy
  have e : w⁻¹ * (x * y * w * (x * y)⁻¹) =
      (w⁻¹ * (x * w * x⁻¹)) * (x * (w⁻¹ * (y * w * y⁻¹)) * x⁻¹) := by group
  rw [e, (Commute.mul_pow (H.stage.comm _ hcx _ hxcy) _), conj_pow,
    hD.conj_szA₁ hx _ (H.stage.pow_mem_szA₁ hcy),
    H.coords.mul _ (H.stage.pow_mem_szA₁ hcx) _ (H.stage.pow_mem_szA₁ hcy)]

theorem mem_U_of_transHom_eq_one (z : U') (h1 : hD.transHom z = 1) : (z : G) ∈ U := by
  refine hD.mem_U z z.2 ?_
  have := congrArg Multiplicative.toAdd h1
  rwa [transHom_apply] at this

theorem comm_mem_U₁ {x y : G} (hx : x ∈ U') (hy : y ∈ U') : x * y * x⁻¹ * y⁻¹ ∈ U₁ := by
  have hz : x * y * x⁻¹ * y⁻¹ ∈ U' := mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have hzU : x * y * x⁻¹ * y⁻¹ ∈ U := by
    refine hD.mem_U_of_transHom_eq_one ⟨_, hz⟩ ?_
    have e : (⟨x * y * x⁻¹ * y⁻¹, hz⟩ : U') = ⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (hD.transHom ⟨x, hx⟩)]
    group
  refine H.mem_U₁_of_M_eq_zero hzU fun w hw => ?_
  have hxy := mul_mem hx hy
  have hxyx := mul_mem hxy (inv_mem hx)
  have hinv : ∀ z ∈ U', v ((w⁻¹ * (z⁻¹ * w * z⁻¹⁻¹)) ^ 2 ^ k) = v ((w⁻¹ * (z * w * z⁻¹)) ^ 2 ^ k) := by
    intro z hz'
    have e := hD.M_mul hz' (inv_mem hz') hw
    rw [show w⁻¹ * (z * z⁻¹ * w * (z * z⁻¹)⁻¹) = 1 by group, one_pow, H.coords.v_one] at e
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination -e - v ((w⁻¹ * (z * w * z⁻¹)) ^ 2 ^ k) * h2
  rw [hD.M_mul hxyx (inv_mem hy) hw, hD.M_mul hxy (inv_mem hx) hw, hD.M_mul hx hy hw,
    hinv x hx, hinv y hy]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination (v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k) + v ((w⁻¹ * (y * w * y⁻¹)) ^ 2 ^ k)) * h2

theorem sq_mem_U₁ {x : G} (hx : x ∈ U') : x ^ 2 ∈ U₁ := by
  have hz : x ^ 2 ∈ U' := pow_mem hx 2
  have hzU : x ^ 2 ∈ U := by
    refine hD.mem_U_of_transHom_eq_one ⟨_, hz⟩ ?_
    have e : (⟨x ^ 2, hz⟩ : U') = ⟨x, hx⟩ ^ 2 := rfl
    rw [e, map_pow, transHom_apply, sq, ← ofAdd_add, CharTwo.add_self_eq_zero]
    rfl
  refine H.mem_U₁_of_M_eq_zero hzU fun w hw => ?_
  rw [sq, hD.M_mul hx hx hw]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k) * h2

theorem fix_d {w : G} (hw : w ∈ U') (hwd : w⁻¹ * (d⁻¹ * w * d) ∈ U₁) :
    w ∈ U₁ ∨ t⁻¹ * w ∈ U₁ := by
  have hdN : d⁻¹ ∈ normalizer (U : Set G) := inv_mem H.d_mem_normalizer_U
  have hwN := hD.le hw
  have hdw : d⁻¹ * w * d ∈ normalizer (U : Set G) :=
    mul_mem (mul_mem hdN hwN) (by simpa using inv_mem hdN)
  have hwdU : w⁻¹ * (d⁻¹ * w * d) ∈ U := H.stage.U₁_le hwd
  have h1 : H.perm ⟨d⁻¹ * w * d, hdw⟩ = H.perm ⟨w, hwN⟩ := by
    have h2 := H.perm_eq_one_of_mem_U ⟨w⁻¹ * (d⁻¹ * w * d), le_normalizer hwdU⟩ hwdU
    have e : (⟨w⁻¹ * (d⁻¹ * w * d), le_normalizer hwdU⟩ : normalizer (U : Set G)) =
        ⟨w, hwN⟩⁻¹ * ⟨d⁻¹ * w * d, hdw⟩ := rfl
    rw [e, map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2.symm
  set δ : normalizer (U : Set G) := ⟨d⁻¹, hdN⟩ with hδ
  have e : (⟨d⁻¹ * w * d, hdw⟩ : normalizer (U : Set G)) = δ * ⟨w, hwN⟩ * δ⁻¹ :=
    Subtype.ext (by simp [hδ])
  have hδ0 : H.perm δ⁻¹ 0 = 0 := by
    have h3 := H.perm_d_inv 0
    rw [mul_zero] at h3
    rw [← h3, ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Equiv.Perm.one_apply,
      h3]
  have h4 : H.perm ⟨d⁻¹ * w * d, hdw⟩ 0 = H.perm ⟨w, hwN⟩ 0 := by rw [h1]
  rw [e, map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hδ0, H.perm_d_inv] at h4
  have hc0 : H.perm ⟨w, hwN⟩ 0 = 0 := by
    have h5 : (μ - 1) * H.perm ⟨w, hwN⟩ 0 = 0 := by linear_combination h4
    exact (mul_eq_zero.mp h5).resolve_left (sub_ne_zero.mpr H.mu_ne_one)
  have hwU := hD.mem_U w hw hc0
  rcases H.stage.mem_or_mul_t_mem hwU with h6 | h6
  · exact Or.inl h6
  · right
    have h7 := (mem_normalizer_iff.mp H.stage.t_mem_normalizer_U₁ _).mp h6
    rwa [show t * (w * t) * t⁻¹ = t * w by group, show t * w = t⁻¹ * w by rw [H.stage.t_inv]]
      at h7

theorem exists_U₁' :
    ∃ U₁' : Subgroup G, U₁ ≤ U₁' ∧ U₁' ≤ U' ∧ U' ≤ normalizer (U₁' : Set G) ∧
      t ∉ U₁' ∧ U₁' ⊔ zpowers t = U' ∧ d ∈ normalizer (U₁' : Set G) ∧ U₁' ⊓ U = U₁ := by
  have hdt : d * t = t * d := mem_centralizer_singleton_iff.mp H.stage.d_norm.2
  obtain ⟨U₁', hHU₁, hU₁U, hUU₁, htU₁, hsupU₁, hdU₁⟩ := exists_complement_of_coprime
    (H.stage.U₁_le.trans hD.U_le) (hD.le.trans H.normalizer_U_le_normalizer_U₁)
    (fun x hx y hy => hD.comm_mem_U₁ hx hy) (fun x hx => hD.sq_mem_U₁ hx)
    (hD.normal H.d_mem_normalizer_U) H.stage.d_mem_U₁ H.stage.d_odd
    (hD.U_le H.stage.t_mem_U) H.stage.t_not_mem hdt (fun w hw hwd => hD.fix_d hw hwd)
  refine ⟨U₁', hHU₁, hU₁U, hUU₁, htU₁, hsupU₁, hdU₁, le_antisymm (fun x hx => ?_)
    (le_inf hHU₁ H.stage.U₁_le)⟩
  obtain ⟨hxU₁', hxU⟩ := mem_inf.mp hx
  rcases H.stage.mem_or_mul_t_mem hxU with h1 | h1
  · exact h1
  · exfalso
    apply htU₁
    have e : t = x⁻¹ * (x * t) := by group
    rw [e]
    exact mul_mem (inv_mem hxU₁') (hHU₁ h1)

end NextUData

end U3C1Next

end CFSG.SeitzReduction.RankOne
