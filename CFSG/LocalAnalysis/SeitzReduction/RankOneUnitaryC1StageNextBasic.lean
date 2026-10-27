module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1StageBranchNu

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1Stage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ}

section Basic

variable (h : U3C1Stage G L f t T d V U U₁ k)
include h

theorem inv_V₁ (hν : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1) {w : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) : t * w * t⁻¹ = w⁻¹ := by
  have e := hν w hw
  rw [h.sq_mul_t] at e
  exact eq_inv_of_mul_eq_one_right e

theorem sq_mul_mul_t_V₁ (hν : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1)
    {y w : G} (hy : y ∈ szT₁ L T) (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    (y * w * t) ^ 2 = y ^ 2 := by
  have e1 : t * y = y * t := (h.t_comm hy).symm
  have e3 : w * y = y * w := (mem_centralizer_iff.mp (mem_inf.mp hw).2 y hy).symm
  have e2 : t * w = w⁻¹ * t := by
    calc t * w = (t * w * t⁻¹) * t := by group
      _ = w⁻¹ * t := by rw [h.inv_V₁ hν hw]
  calc (y * w * t) ^ 2 = y * w * (t * y) * w * t := by rw [sq]; group
    _ = y * (w * y) * (t * w) * t := by rw [e1]; group
    _ = y * (y * w) * (w⁻¹ * t) * t := by rw [e3, e2]
    _ = y * y * (t * t) := by group
    _ = y ^ 2 := by rw [h.t_mul_self, mul_one, sq]

theorem exists_mul_V₁ (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) {z : G}
    (hz : z ∈ U₁) : ∃ y ∈ szT₁ L T, ∃ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), z = y * w := by
  have hTN : szT₁ L T ≤ normalizer ((U₁ ⊓ centralizer (szT₁ L T : Set G) : Subgroup G) : Set G) :=
    fun y hy => mem_normalizer_of_forall_inv_mul_mul_mem fun w hw => by
      rw [mem_centralizer_iff.mp (mem_inf.mp hw).2 _ (inv_mem hy), inv_mul_cancel_right]
      exact hw
  have hz' : z ∈ ((szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)) : Subgroup G) : Set G) := by
    rw [← hlam]
    exact hz
  rw [coe_mul_of_left_le_normalizer_right _ _ hTN] at hz'
  obtain ⟨y, hy, w, hw, rfl⟩ := hz'
  exact ⟨y, hy, w, hw, rfl⟩

theorem mem_T₁_of_comm_mul_t (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1) {w : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) {z : G} (hz : z ∈ U₁)
    (hzc : z * (w * t) = (w * t) * z) : z ∈ szT₁ L T := by
  obtain ⟨-, hcomm, -, hΩ, -⟩ := h.nextConf hμV hlam hν
  obtain ⟨y, hy, w', hw', rfl⟩ := h.exists_mul_V₁ hlam hz
  have hwy : w * y = y * w := (mem_centralizer_iff.mp (mem_inf.mp hw).2 y hy).symm
  have hww' : w * w'⁻¹ = w'⁻¹ * w := hcomm _ hw _ (inv_mem hw')
  have e : (w * t) * (y * w') * (w * t)⁻¹ = y * w'⁻¹ := by
    have e1 : (w * t) * (y * w') * (w * t)⁻¹ = w * y * (t * w' * t⁻¹) * w⁻¹ := by
      rw [show w * t * (y * w') * (w * t)⁻¹ = w * (t * y) * w' * t⁻¹ * w⁻¹ by group,
        ← h.t_comm hy]
      group
    rw [e1, h.inv_V₁ hν hw', hwy, mul_assoc y w w'⁻¹, hww']
    group
  have e2 : y * w' = y * w'⁻¹ := by
    rw [← e, ← hzc]
    group
  have hw'2 : w' ^ 2 = 1 := by
    have e3 : w' = w'⁻¹ := mul_left_cancel e2
    rw [sq]
    nth_rewrite 2 [e3]
    exact mul_inv_cancel w'
  exact mul_mem hy (szA₁_le _ (hΩ w' hw' hw'2))

theorem comm_t_mem_V₁_of_normalizer (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1) {n : G}
    (hn : n ∈ normalizer (U : Set G)) :
    n * t * n⁻¹ * t⁻¹ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) := by
  have hxU : n * t * n⁻¹ ∈ U := (mem_normalizer_iff.mp hn t).mp h.t_mem_U
  have hxt := (h.mem_or_mul_t_mem hxU).resolve_left (h.conj_not_mem_U₁ n)
  obtain ⟨y, hy, w, hw, hyw⟩ := h.exists_mul_V₁ hlam hxt
  have hx : n * t * n⁻¹ = y * w * t := by
    rw [← hyw, mul_assoc (n * t * n⁻¹) t t, h.t_mul_self, mul_one]
  have hsq : (y * w * t) ^ 2 = 1 := by
    rw [← hx, sq, show n * t * n⁻¹ * (n * t * n⁻¹) = n * (t * t) * n⁻¹ by group, h.t_mul_self,
      mul_one, mul_inv_cancel]
  rw [h.sq_mul_mul_t_V₁ hν hy hw] at hsq
  have hyA := h.mem_szA₁_of_sq_eq_one hy hsq
  rw [hx, show y * w * t * t⁻¹ = y * w by group]
  exact mul_mem (h.V_le_V₁ (h.le hyA)) hw

theorem normalizer_U_le_normalizer_T₁ (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1) :
    normalizer (U : Set G) ≤ normalizer (szT₁ L T : Set G) := by
  have key : ∀ n ∈ normalizer (U : Set G), ∀ y ∈ szT₁ L T, n * y * n⁻¹ ∈ szT₁ L T := by
    intro n hn y hy
    have hσ := h.comm_t_mem_V₁_of_normalizer hlam hν hn
    have hyU₁ := h.conj_mem_U₁_of_normalizer hμV hn (h.T₁_le_U₁ hy)
    refine h.mem_T₁_of_comm_mul_t hμV hlam hν hσ hyU₁ ?_
    rw [show n * t * n⁻¹ * t⁻¹ * t = n * t * n⁻¹ by group]
    calc n * y * n⁻¹ * (n * t * n⁻¹) = n * (y * t) * n⁻¹ := by group
      _ = n * (t * y) * n⁻¹ := by rw [h.t_comm hy]
      _ = n * t * n⁻¹ * (n * y * n⁻¹) := by group
  intro n hn
  refine mem_normalizer_iff.mpr fun y => ⟨key n hn y, fun hy => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ hy
  rwa [show n⁻¹ * (n * y * n⁻¹) * n⁻¹⁻¹ = y by group] at this

theorem normalizer_U_le_normalizer_V₁ (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1) :
    normalizer (U : Set G) ≤
      normalizer ((U₁ ⊓ centralizer (szT₁ L T : Set G) : Subgroup G) : Set G) := by
  intro n hn
  have hT := h.normalizer_U_le_normalizer_T₁ hμV hlam hν hn
  have hU₁ : ∀ g ∈ normalizer (U : Set G), ∀ w ∈ U₁, g * w * g⁻¹ ∈ U₁ := fun g hg w hw =>
    h.conj_mem_U₁_of_normalizer hμV hg hw
  refine mem_normalizer_iff.mpr fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · refine mem_inf.mpr ⟨hU₁ n hn w (mem_inf.mp hw).1, mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy' : n⁻¹ * y * n ∈ szT₁ L T := by
      simpa using (mem_normalizer_iff.mp (inv_mem hT) y).mp hy
    have e := mem_centralizer_iff.mp (mem_inf.mp hw).2 _ hy'
    calc y * (n * w * n⁻¹) = n * ((n⁻¹ * y * n) * w) * n⁻¹ := by group
      _ = n * (w * (n⁻¹ * y * n)) * n⁻¹ := by rw [e]
      _ = n * w * n⁻¹ * y := by group
  · obtain ⟨hwU, hwC⟩ := mem_inf.mp hw
    have hw' : w ∈ U₁ := by
      have := hU₁ n⁻¹ (inv_mem hn) _ hwU
      rwa [show n⁻¹ * (n * w * n⁻¹) * n⁻¹⁻¹ = w by group] at this
    refine mem_inf.mpr ⟨hw', mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy' : n * y * n⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hT y).mp hy
    have e := mem_centralizer_iff.mp hwC _ hy'
    calc y * w = n⁻¹ * (n * y * n⁻¹ * (n * w * n⁻¹)) * n := by group
      _ = n⁻¹ * (n * w * n⁻¹ * (n * y * n⁻¹)) * n := by rw [e]
      _ = w * y := by group

theorem pow_mem_szA₁_V₁ {w : G} (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    w ^ 2 ^ (k + 1) ∈ szA₁ (szT₁ L T) := by
  rw [pow_succ', pow_mul]
  exact h.pow_mem_szA₁ (h.sq_mem_V (mem_inf.mp hw).1)

end Basic

section Coords

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {v : G → K}
  {μ : K} (h : U3C1Stage G L f t T d V U U₁ k) (hK : Fintype.card K = 2 ^ f)
  (hc : U3A₁Coords (szA₁ (szT₁ L T)) d v μ)
include h hK hc

theorem S_eq_of_mem_V₁ (hν : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1) {w : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    v ((w * t * w⁻¹ * t⁻¹) ^ 2 ^ k) = v (w ^ 2 ^ (k + 1)) := by
  rw [SzC1.comm_eq_sq_of_inv (h.inv_V₁ hν hw), ← pow_mul, ← pow_succ']

theorem X_mul (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) {w w' : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hw' : w' ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    v ((w * w') ^ 2 ^ (k + 1)) = v (w ^ 2 ^ (k + 1)) + v (w' ^ 2 ^ (k + 1)) := by
  rw [(Commute.mul_pow (h.V₁_comm hμV hlam w hw w' hw') _),
    hc.mul _ (h.pow_mem_szA₁_V₁ hw) _ (h.pow_mem_szA₁_V₁ hw')]

theorem X_eq_zero_of_mem_V {r : G} (hr : r ∈ V) : v (r ^ 2 ^ (k + 1)) = 0 := by
  rw [h.pow r hr, hc.v_one]

theorem mem_V_of_X_eq_zero (hν : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1)
    {w : G} (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) (h0 : v (w ^ 2 ^ (k + 1)) = 0) :
    w ∈ V := by
  refine h.mem_V_of_mem_V₁_of_mem_sup hw (h.mem_sup_of_S_eq_zero hK hc (mem_inf.mp hw).1 ?_)
  rw [h.S_eq_of_mem_V₁ hK hc hν hw, h0]

theorem X_surj (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w)
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1) (s : K) :
    ∃ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), v (w ^ 2 ^ (k + 1)) = s := by
  obtain ⟨w, hw, hws⟩ := h.S_surj_V₁ hK hc hμ hlam s
  exact ⟨w, hw, by rw [← h.S_eq_of_mem_V₁ hK hc hν hw, hws]⟩

theorem X_eq_iff (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1) {w w' : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hw' : w' ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    v (w ^ 2 ^ (k + 1)) = v (w' ^ 2 ^ (k + 1)) ↔ w⁻¹ * w' ∈ V := by
  have hinv : w⁻¹ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) := inv_mem hw
  have hadd := h.X_mul hK hc hμV hlam hinv hw'
  have hX : v (w⁻¹ ^ 2 ^ (k + 1)) = v (w ^ 2 ^ (k + 1)) := by
    have hA := h.pow_mem_szA₁_V₁ hw
    have hb : (w ^ 2 ^ (k + 1))⁻¹ = w ^ 2 ^ (k + 1) :=
      inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hc.sq_eq_one hA)
    rw [inv_pow, hb]
  rw [hX] at hadd
  constructor
  · intro heq
    refine h.mem_V_of_X_eq_zero hK hc hν (mul_mem hinv hw') ?_
    rw [hadd, heq, CharTwo.add_self_eq_zero]
  · intro hV
    have h0 := h.X_eq_zero_of_mem_V hK hc hV
    rw [hadd] at h0
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h0 - v (w' ^ 2 ^ (k + 1)) * h2

end Coords

end U3C1Stage

end CFSG.SeitzReduction.RankOne
