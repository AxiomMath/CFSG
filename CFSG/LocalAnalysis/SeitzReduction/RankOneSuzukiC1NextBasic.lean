module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1BranchFam

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace SzC1Stage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f a : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ}

section Basic

variable (h : SzC1Stage G L f a t T d V U U₁ k)
include h

theorem szR_V₁_eq (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) :
    szR (szT₁ L T) (U₁ ⊓ centralizer (szT₁ L T : Set G)) t = U := by
  rw [szR, ← hlam, h.sup_eq]

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

end Basic

section Coords

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {u v : G → K} {κ : K}
  (h : SzC1Stage G L f a t T d V U U₁ k) (hK : Fintype.card K = 2 ^ f)
  (hc : SzRootCoords (szT₁ L T) a d u v κ)
include h hK hc

theorem comm_t_mem_V₁_of_normalizer
    (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1) {n : G}
    (hn : n ∈ normalizer (U : Set G)) :
    n * t * n⁻¹ * t⁻¹ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) := by
  have hK' := h.card_K hK hc
  obtain ⟨y₀, hy₀, w, hw, hx, -⟩ := h.map_conj_T₁_eq hK hc hμ hlam hn
  have hsq : (y₀ * w * t) ^ 2 = 1 := by
    rw [← hx, sq, show n * t * n⁻¹ * (n * t * n⁻¹) = n * (t * t) * n⁻¹ by group, h.t_mul_self,
      mul_one, mul_inv_cancel]
  rw [h.sq_mul_mul_t_V₁ hν hy₀ hw] at hsq
  have hyA := SzC1.mem_szA₁_of_sq_eq_one hc h.ha hK' hy₀ hsq
  rw [hx, show y₀ * w * t * t⁻¹ = y₀ * w by group]
  exact mul_mem (h.V_le_V₁ (h.le hyA)) hw

theorem normalizer_U_le_normalizer_T₁
    (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1) :
    normalizer (U : Set G) ≤ normalizer (szT₁ L T : Set G) := by
  intro n hn
  have hK' := h.card_K hK hc
  obtain ⟨y₀, hy₀, w, hw, hx, hmap⟩ := h.map_conj_T₁_eq hK hc hμ hlam hn
  have hsq : (y₀ * w * t) ^ 2 = 1 := by
    rw [← hx, sq, show n * t * n⁻¹ * (n * t * n⁻¹) = n * (t * t) * n⁻¹ by group, h.t_mul_self,
      mul_one, mul_inv_cancel]
  rw [h.sq_mul_mul_t_V₁ hν hy₀ hw] at hsq
  have hyA := SzC1.mem_szA₁_of_sq_eq_one hc h.ha hK' hy₀ hsq
  have h1 : (1 : G) ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) := one_mem _
  have hcent := h.cent_eq_of_u_eq hK hc hμ hy₀ (one_mem _)
    (by rw [hc.u_eq_zero_of_mem_szA₁ h.ha hK' hyA, hc.u_one]) hw h1
  have hT := h.T₁_eq_cent hK hc hμ (one_mem _) hc.u_one
  rw [one_mul] at hT
  rw [mul_one, one_mul, ← hT] at hcent
  rw [hcent] at hmap
  exact SzC1.mem_normalizer_of_map_le hmap.le

theorem normalizer_U_le_normalizer_V₁
    (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1) :
    normalizer (U : Set G) ≤
      normalizer ((U₁ ⊓ centralizer (szT₁ L T : Set G) : Subgroup G) : Set G) := by
  intro n hn
  have hT := h.normalizer_U_le_normalizer_T₁ hK hc hμ hlam hν hn
  have hU₁ := h.normalizer_U_le_normalizer_U₁ hK hc hμ hn
  refine mem_normalizer_iff.mpr fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hU₁ w).mp (mem_inf.mp hw).1,
      mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy' : n⁻¹ * y * n ∈ szT₁ L T := by
      simpa using (mem_normalizer_iff.mp (inv_mem hT) y).mp hy
    have e := mem_centralizer_iff.mp (mem_inf.mp hw).2 _ hy'
    calc y * (n * w * n⁻¹) = n * ((n⁻¹ * y * n) * w) * n⁻¹ := by group
      _ = n * (w * (n⁻¹ * y * n)) * n⁻¹ := by rw [e]
      _ = n * w * n⁻¹ * y := by group
  · obtain ⟨hwU, hwC⟩ := mem_inf.mp hw
    refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hU₁ w).mpr hwU,
      mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy' : n * y * n⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hT y).mp hy
    have e := mem_centralizer_iff.mp hwC _ hy'
    have e2 : y * w = w * y := by
      have := congrArg (fun z => n⁻¹ * z * n) e
      calc y * w = n⁻¹ * (n * y * n⁻¹ * (n * w * n⁻¹)) * n := by group
        _ = n⁻¹ * (n * w * n⁻¹ * (n * y * n⁻¹)) * n := this
        _ = w * y := by group
    exact e2

theorem pow_mem_szA₁_V₁ {w : G} (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    w ^ 2 ^ (k + 1) ∈ szA₁ (szT₁ L T) := by
  rw [pow_succ', pow_mul]
  exact h.pow_mem_szA₁ (h.sq_mem_V (mem_inf.mp hw).1)

theorem S_eq_of_mem_V₁ (hν : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1) {w : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    v ((w * t * w⁻¹ * t⁻¹) ^ 2 ^ k) = v (w ^ 2 ^ (k + 1)) := by
  rw [SzC1.comm_eq_sq_of_inv (h.inv_V₁ hν hw), ← pow_mul, ← pow_succ']

theorem X_mul (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) {w w' : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hw' : w' ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    v ((w * w') ^ 2 ^ (k + 1)) = v (w ^ 2 ^ (k + 1)) + v (w' ^ 2 ^ (k + 1)) := by
  rw [(Commute.mul_pow (h.V₁_comm hμ hlam w hw w' hw') _),
    hc.v_mul_szA₁ h.ha (h.card_K hK hc) (h.pow_mem_szA₁_V₁ hK hc hw) (h.pow_mem_szA₁_V₁ hK hc hw')]

theorem X_eq_zero_of_mem_V {r : G} (hr : r ∈ V) : v (r ^ 2 ^ (k + 1)) = 0 := by
  rw [h.pow r hr, hc.v_one]

theorem mem_V_of_X_eq_zero (hν : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1)
    {w : G} (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) (h0 : v (w ^ 2 ^ (k + 1)) = 0) :
    w ∈ V := by
  refine h.mem_V_of_mem_V₁_of_mem_sup hw (h.mem_sup_of_S_eq_zero hK hc (mem_inf.mp hw).1 ?_)
  rw [h.S_eq_of_mem_V₁ hK hc hν hw, h0]

theorem X_surj (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w)
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1) (s : K) :
    ∃ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), v (w ^ 2 ^ (k + 1)) = s := by
  obtain ⟨w, hw, hws⟩ := h.S_surj_V₁ hK hc hκ hlam s
  exact ⟨w, hw, by rw [← h.S_eq_of_mem_V₁ hK hc hν hw, hws]⟩

theorem X_eq_iff (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1) {w w' : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hw' : w' ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    v (w ^ 2 ^ (k + 1)) = v (w' ^ 2 ^ (k + 1)) ↔ w⁻¹ * w' ∈ V := by
  have hinv : w⁻¹ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) := inv_mem hw
  have hadd := h.X_mul hK hc hμ hlam hinv hw'
  have hX : v (w⁻¹ ^ 2 ^ (k + 1)) = v (w ^ 2 ^ (k + 1)) := by
    rw [inv_pow, hc.v_inv_szA₁ h.ha (h.card_K hK hc) (h.pow_mem_szA₁_V₁ hK hc hw)]
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

end SzC1Stage

end CFSG.SeitzReduction.RankOne
