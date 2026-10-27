module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L125Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L127Base

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec125_sqrt_conj {t k : G} (htsq : t * t = 1) (hk : Odd (orderOf k))
    (hinv : t * k * t⁻¹ = k⁻¹) : ∃ κ ∈ zpowers k, κ * t * κ⁻¹ = t * k := by
  obtain ⟨r, hr⟩ := hk
  have hone : k ^ (2 * r) * k = 1 := by
    rw [← pow_succ, ← hr]
    exact pow_orderOf_eq_one k
  have hsq : k ^ r * k ^ r = k⁻¹ := by
    rw [← pow_add, ← two_mul]
    exact eq_inv_of_mul_eq_one_left hone
  have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right htsq
  have hconj : t * k ^ r * t⁻¹ = (k ^ r)⁻¹ := by
    rw [← conj_pow, hinv, inv_pow]
  refine ⟨k ^ r, Subgroup.pow_mem _ (Subgroup.mem_zpowers k) r, ?_⟩
  have h1 : k ^ r * t = t * (k ^ r)⁻¹ := by
    calc k ^ r * t = (t * t) * k ^ r * t := by rw [htsq, one_mul]
      _ = t * (t * k ^ r * t⁻¹) := by rw [ht]; group
      _ = t * (k ^ r)⁻¹ := by rw [hconj]
  calc k ^ r * t * (k ^ r)⁻¹ = t * ((k ^ r)⁻¹ * (k ^ r)⁻¹) := by rw [h1]; group
    _ = t * (k ^ r * k ^ r)⁻¹ := by rw [mul_inv_rev]
    _ = t * k := by rw [hsq, inv_inv]

namespace Sec125Core

variable {t : G} {V E : Subgroup G}

theorem exists_conj_of_involution (h : Sec125Core t V E) {K : Subgroup G}
    (hKc : ∀ v ∈ V, ∀ k ∈ K, v * k = k * v) (hKo : ∀ k ∈ K, Odd (orderOf k))
    (hKt : ∀ k ∈ K, t * k * t⁻¹ ∈ K) {d : G} (hd : d ∈ V ⊔ K) (hinv : t * d * (t * d) = 1) :
    ∃ δ ∈ V ⊔ K, δ * t * δ⁻¹ = t * d := by
  have hKN : K ≤ normalizer (V : Set G) := fun k hk =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun v hv => hKc v hv k hk)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left V K hKN] at hd
  obtain ⟨v, hv, k, hk, rfl⟩ := hd
  have key : ∀ v' ∈ V, ∀ k' ∈ K, v' * k' * (v * k) = 1 → v' = v⁻¹ ∧ k' = k⁻¹ := by
    intro v' hv' k' hk' heq
    have h2 : (v' * v) * (k' * k) = 1 := by
      calc (v' * v) * (k' * k) = v' * (v * k') * k := by group
        _ = v' * (k' * v) * k := by rw [hKc v hv k' hk']
        _ = v' * k' * (v * k) := by group
        _ = 1 := heq
    have hxV : v' * v ∈ V := mul_mem hv' hv
    have hxK : v' * v ∈ K := by
      rw [eq_inv_of_mul_eq_one_left h2]
      exact inv_mem (mul_mem hk' hk)
    have hx1 : v' * v = 1 := by
      have hdvd : orderOf (v' * v) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h.sq _ hxV)
      obtain ⟨m, hm⟩ := hKo _ hxK
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      exact orderOf_eq_one_iff.mp (by omega)
    rw [hx1, one_mul] at h2
    exact ⟨eq_inv_of_mul_eq_one_left hx1, eq_inv_of_mul_eq_one_left h2⟩
  have hv' : t * v * t⁻¹ ∈ V := h.tnorm v hv
  have hk' : t * k * t⁻¹ ∈ K := hKt k hk
  have h1 : (t * v * t⁻¹) * (t * k * t⁻¹) * (v * k) = 1 := by
    have e : t * (v * k) * (t * (v * k)) =
        (t * v * t⁻¹) * (t * k * t⁻¹) * (t * t) * (v * k) := by group
    rw [e, h.tsq, mul_one] at hinv
    exact hinv
  obtain ⟨hv'eq, hk'eq⟩ := key _ hv' _ hk' h1
  have hvt : t * v = v * t := by
    calc t * v = (t * v * t⁻¹) * t := by group
      _ = v * t := by rw [hv'eq, h.inv_eq hv]
  obtain ⟨w, hw, hwt⟩ := h.trans v hv hvt.symm
  obtain ⟨κ, hκ, hκt⟩ := sec125_sqrt_conj h.tsq (hKo k hk) hk'eq
  have hκK : κ ∈ K := Subgroup.zpowers_le.mpr hk hκ
  refine ⟨w * κ, mul_mem (Subgroup.mem_sup_left hw) (Subgroup.mem_sup_right hκK), ?_⟩
  have hwk : w * k * w⁻¹ = k := by rw [hKc w hw k hk]; group
  calc w * κ * t * (w * κ)⁻¹ = w * (κ * t * κ⁻¹) * w⁻¹ := by group
    _ = w * (t * k) * w⁻¹ := by rw [hκt]
    _ = (w * t * w⁻¹) * (w * k * w⁻¹) := by group
    _ = (v * t) * k := by rw [hwt, hwk]
    _ = t * (v * k) := by rw [← hvt]; group

theorem exists_comm_of_beta (h : Sec125Core t V E) {K : Subgroup G}
    (hD : centralizer (V : Set G) = V ⊔ K) (hKo : ∀ k ∈ K, Odd (orderOf k))
    (hKt : ∀ k ∈ K, t * k * t⁻¹ ∈ K) {n : G} (hn : n ∈ normalizer (V : Set G))
    (hnt : betaOf V n * betaOf V t = betaOf V t * betaOf V n) :
    ∃ c ∈ normalizer (V : Set G), c * t = t * c ∧ betaOf V c = betaOf V n := by
  have ht : t ∈ normalizer (V : Set G) := h.t_mem_normalizer
  have hKc : ∀ v ∈ V, ∀ k ∈ K, v * k = k * v := fun v hv k hk =>
    Subgroup.mem_centralizer_iff.mp (by rw [hD]; exact Subgroup.mem_sup_right hk) v hv
  have hbeta : betaOf V (n * t) = betaOf V (t * n) := by
    rw [sec127_betaOf_mul hn ht, sec127_betaOf_mul ht hn]
    exact hnt
  have hnt' : (n * t)⁻¹ * (t * n) ∈ centralizer (V : Set G) :=
    (sec127_betaOf_eq_iff (mul_mem hn ht) (mul_mem ht hn)).mp hbeta
  have e : t * ((n * t)⁻¹ * (t * n)) = n⁻¹ * t * n := by group
  have hinv : t * ((n * t)⁻¹ * (t * n)) * (t * ((n * t)⁻¹ * (t * n))) = 1 := by
    rw [e]
    calc n⁻¹ * t * n * (n⁻¹ * t * n) = n⁻¹ * (t * t) * n := by group
      _ = 1 := by rw [h.tsq]; group
  obtain ⟨δ, hδ, hδt⟩ := h.exists_conj_of_involution hKc hKo hKt (by rw [← hD]; exact hnt') hinv
  have hδD : δ ∈ centralizer (V : Set G) := by rw [hD]; exact hδ
  have hδN : δ ∈ normalizer (V : Set G) := Subgroup.centralizer_le_normalizer _ hδD
  refine ⟨n * δ, mul_mem hn hδN, ?_, ?_⟩
  · rw [e] at hδt
    calc n * δ * t = n * (δ * t * δ⁻¹) * δ := by group
      _ = n * (n⁻¹ * t * n) * δ := by rw [hδt]
      _ = t * (n * δ) := by group
  · rw [sec127_betaOf_mul hn hδN, (sec127_betaOf_eq_one_iff hδN).mpr hδD, mul_one]

end Sec125Core

end CFSG.OddStandard.SmallF3.Omega
