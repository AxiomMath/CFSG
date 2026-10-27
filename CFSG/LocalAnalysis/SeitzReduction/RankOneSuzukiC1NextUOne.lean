module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1NextU

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace SzC1Next

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f a : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {u v : G → K} {κ : K} (H : SzC1Next G L f a t T d V U U₁ k K u v κ)

section NoE

include H

theorem U₁_le_centralizer_V₁ :
    U₁ ≤ centralizer ((U₁ ⊓ centralizer (szT₁ L T : Set G) : Subgroup G) : Set G) := by
  intro x hx
  obtain ⟨y, hy, w, hw, rfl⟩ := H.stage.exists_mul_of_mem_U₁ H.lam hx
  exact mul_mem (mem_centralizer_iff.mpr fun z hz => (mem_centralizer_iff.mp (mem_inf.mp hz).2 y hy).symm)
    (mem_centralizer_iff.mpr fun z hz => H.V₁_comm hz hw)

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
    H.coords.v_inv_szA₁ H.stage.ha H.card_K' (H.stage.pow_mem_szA₁_V₁ H.card_K H.coords hw)]

theorem mem_U₁_of_M_eq_zero {z : G} (hz : z ∈ U)
    (hM : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), v ((w⁻¹ * (z * w * z⁻¹)) ^ 2 ^ k) = 0) :
    z ∈ U₁ := by
  rcases H.stage.mem_or_mul_t_mem hz with h | h
  · exact h
  · exfalso
    have e := H.M_eq_X_of_mul_t h (H.sec_mem 1)
    rw [hM _ (H.sec_mem 1), H.sec_X] at e
    exact zero_ne_one e

end NoE

variable
  {E : Subgroup (Equiv.Perm K)} (hE : H.RegData E)
include H hE

theorem chi_mem_V_of_mem_nextU {x : G} (hx : x ∈ H.nextU E) {w : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) : w⁻¹ * (x * w * x⁻¹) ∈ V :=
  (H.X_eq_iff hw (H.conj_mem_V₁ (H.nextU_le hE hx) hw)).mp (H.X_conj_of_mem_nextU hE hx hw).symm

theorem M_mul_of_mem_nextU {x y : G} (hx : x ∈ H.nextU E) (hy : y ∈ H.nextU E) {w : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    v ((w⁻¹ * (x * y * w * (x * y)⁻¹)) ^ 2 ^ k) =
      v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k) + v ((w⁻¹ * (y * w * y⁻¹)) ^ 2 ^ k) := by
  have hcx := H.chi_mem_V_of_mem_nextU hE hx hw
  have hcy := H.chi_mem_V_of_mem_nextU hE hy hw
  have hxcy : x * (w⁻¹ * (y * w * y⁻¹)) * x⁻¹ ∈ V :=
    (mem_normalizer_iff.mp (H.stage.normalizer_U_le_normalizer_V (H.nextU_le hE hx)) _).mp hcy
  have e : w⁻¹ * (x * y * w * (x * y)⁻¹) =
      (w⁻¹ * (x * w * x⁻¹)) * (x * (w⁻¹ * (y * w * y⁻¹)) * x⁻¹) := by group
  rw [e, (Commute.mul_pow (H.stage.comm _ hcx _ hxcy) _), conj_pow,
    H.conj_szA₁_of_mem_nextU hE hx _ (H.stage.pow_mem_szA₁ hcy),
    H.coords.v_mul_szA₁ H.stage.ha H.card_K' (H.stage.pow_mem_szA₁ hcx) (H.stage.pow_mem_szA₁ hcy)]

theorem M_inv_of_mem_nextU {x : G} (hx : x ∈ H.nextU E) {w : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    v ((w⁻¹ * (x⁻¹ * w * x⁻¹⁻¹)) ^ 2 ^ k) = v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k) := by
  have e := H.M_mul_of_mem_nextU hE hx (inv_mem hx) hw
  rw [show w⁻¹ * (x * x⁻¹ * w * (x * x⁻¹)⁻¹) = 1 by group, one_pow, H.coords.v_one] at e
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination -e - v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k) * h2

theorem comm_mem_U₁_of_mem_nextU {x y : G} (hx : x ∈ H.nextU E) (hy : y ∈ H.nextU E) :
    x * y * x⁻¹ * y⁻¹ ∈ U₁ := by
  have hz : x * y * x⁻¹ * y⁻¹ ∈ H.nextU E :=
    mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have hxN := H.nextU_le hE hx
  have hyN := H.nextU_le hE hy
  have hzU : x * y * x⁻¹ * y⁻¹ ∈ U := by
    refine H.mem_U_of_perm_eq_one ⟨_, H.nextU_le hE hz⟩ ?_
    have e : (⟨x * y * x⁻¹ * y⁻¹, H.nextU_le hE hz⟩ : normalizer (U : Set G)) =
        ⟨x, hxN⟩ * ⟨y, hyN⟩ * ⟨x, hxN⟩⁻¹ * ⟨y, hyN⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv,
      hE.comm _ (H.perm_mem_of_mem_nextU hE hx) _ (H.perm_mem_of_mem_nextU hE hy)]
    group
  refine H.mem_U₁_of_M_eq_zero hzU fun w hw => ?_
  have hxy := mul_mem hx hy
  have hxyx := mul_mem hxy (inv_mem hx)
  rw [H.M_mul_of_mem_nextU hE hxyx (inv_mem hy) hw, H.M_mul_of_mem_nextU hE hxy (inv_mem hx) hw,
    H.M_mul_of_mem_nextU hE hx hy hw, H.M_inv_of_mem_nextU hE hx hw,
    H.M_inv_of_mem_nextU hE hy hw]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination (v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k) + v ((w⁻¹ * (y * w * y⁻¹)) ^ 2 ^ k)) * h2

theorem sq_mem_U₁_of_mem_nextU {x : G} (hx : x ∈ H.nextU E) : x ^ 2 ∈ U₁ := by
  have hz : x ^ 2 ∈ H.nextU E := pow_mem hx 2
  have hxN := H.nextU_le hE hx
  have hzU : x ^ 2 ∈ U := by
    refine H.mem_U_of_perm_eq_one ⟨_, H.nextU_le hE hz⟩ ?_
    have e : (⟨x ^ 2, H.nextU_le hE hz⟩ : normalizer (U : Set G)) = ⟨x, hxN⟩ ^ 2 := rfl
    rw [e, map_pow]
    exact hE.sq _ (H.perm_mem_of_mem_nextU hE hx)
  refine H.mem_U₁_of_M_eq_zero hzU fun w hw => ?_
  rw [sq, H.M_mul_of_mem_nextU hE hx hx hw]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k) * h2


theorem fix_d_of_mem_nextU {w : G} (hw : w ∈ H.nextU E)
    (hwd : w⁻¹ * (d⁻¹ * w * d) ∈ U₁) : w ∈ U₁ ∨ t⁻¹ * w ∈ U₁ := by
  have hdN : d⁻¹ ∈ normalizer (U : Set G) := inv_mem H.stage.d_mem_normalizer_U
  have hwN := H.nextU_le hE hw
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
  have hμ1 := (SzRCoords2.kappa_ne_one H.stage.ha H.card_K' H.gen_mu).2
  have hc0 : H.perm ⟨w, hwN⟩ 0 = 0 := by
    have h5 : (κ ^ (2 ^ (a + 1) + 1) - 1) * H.perm ⟨w, hwN⟩ 0 = 0 := by linear_combination h4
    exact (mul_eq_zero.mp h5).resolve_left (sub_ne_zero.mpr hμ1)
  have hwU := H.mem_U_of_mem_nextU hE hw hc0
  rcases H.stage.mem_or_mul_t_mem hwU with h6 | h6
  · exact Or.inl h6
  · right
    have h7 := (mem_normalizer_iff.mp H.stage.t_mem_normalizer_U₁ _).mp h6
    rwa [show t * (w * t) * t⁻¹ = t * w by group, show t * w = t⁻¹ * w by rw [H.stage.t_inv]]
      at h7

theorem exists_U₁' :
    ∃ U₁' : Subgroup G, U₁ ≤ U₁' ∧ U₁' ≤ H.nextU E ∧ H.nextU E ≤ normalizer (U₁' : Set G) ∧
      t ∉ U₁' ∧ U₁' ⊔ zpowers t = H.nextU E ∧ d ∈ normalizer (U₁' : Set G) ∧ U₁' ⊓ U = U₁ := by
  have hdt : d * t = t * d := mem_centralizer_singleton_iff.mp H.stage.d_norm.2
  obtain ⟨U₁', hHU₁, hU₁U, hUU₁, htU₁, hsupU₁, hdU₁⟩ := exists_complement_of_coprime
    (H.stage.U₁_le.trans (H.U_le_nextU hE))
    ((H.nextU_le hE).trans (H.stage.normalizer_U_le_normalizer_U₁ H.card_K H.coords H.mu))
    (fun x hx y hy => H.comm_mem_U₁_of_mem_nextU hE hx hy)
    (fun x hx => H.sq_mem_U₁_of_mem_nextU hE hx)
    (H.normalizer_le_normalizer_nextU hE H.stage.d_mem_normalizer_U) H.stage.d_mem_U₁
    H.stage.d_odd (H.U_le_nextU hE H.stage.t_mem_U) H.stage.t_not_mem hdt
    (fun w hw hwd => H.fix_d_of_mem_nextU hE hw hwd)
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

end SzC1Next

end CFSG.SeitzReduction.RankOne
