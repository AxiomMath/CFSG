module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55SylTools
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.CoverConj

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.Syl

theorem threeCycle_of_comm_seven {σ c : Perm (Fin 11)} (hσ : orderOf σ = 7) (hc : orderOf c = 3)
    (hcomm : Commute σ c) : c.IsThreeCycle := by
  classical
  have hall : ∀ n ∈ c.cycleType, n = 3 := by
    intro n hn
    have h1 : n ∣ 3 := hc ▸ Equiv.Perm.dvd_of_mem_cycleType hn
    have h2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h <;> omega
  obtain ⟨k, hk⟩ : ∃ k, c.cycleType = Multiset.replicate k 3 :=
    ⟨Multiset.card c.cycleType, Multiset.eq_replicate_card.2 hall⟩
  have hsum : 3 * k ≤ 11 := by
    have h1 := Equiv.Perm.sum_cycleType c
    have h2 := Finset.card_le_univ c.support
    rw [hk, Multiset.sum_replicate] at h1
    simp only [smul_eq_mul, Fintype.card_fin] at h1 h2
    omega
  have hk1 : k ≠ 0 := by
    intro h0
    have h1 : c.cycleType = 0 := by rw [hk, h0]; rfl
    rw [Equiv.Perm.cycleType_eq_zero] at h1
    rw [h1, orderOf_one] at hc
    omega
  have hσc : σ ∈ centralizer ({c} : Set (Perm (Fin 11))) :=
    mem_centralizer_singleton_iff.2 hcomm.eq
  have h7 : 7 ∣ Nat.card (centralizer ({c} : Set (Perm (Fin 11)))) := by
    have := orderOf_dvd_natCard (⟨σ, hσc⟩ : centralizer ({c} : Set (Perm (Fin 11))))
    rwa [Subgroup.orderOf_mk, hσ] at this
  rw [Equiv.Perm.nat_card_centralizer, hk] at h7
  have hfin : (Multiset.replicate k 3).toFinset = {3} := by
    ext x
    simp [hk1]
  rw [hfin, Finset.prod_singleton, Multiset.count_replicate_self, Multiset.sum_replicate,
    Multiset.prod_replicate, Fintype.card_fin, smul_eq_mul] at h7
  have hk3 : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk3 with rfl | rfl | rfl
  · show c.cycleType = {3}
    rw [hk]
    rfl
  · exfalso
    norm_num [Nat.factorial] at h7
  · exfalso
    norm_num [Nat.factorial] at h7

theorem conj_of_order_three_seven {C : Type*} [Group C] {t : C} (ht : t ∈ center C)
    (ht2 : orderOf t = 2) (hZ : Nat.card ↥(center C) = 2)
    (E : (C ⧸ center C) ≃* alternatingGroup (Fin 11))
    {z w z' w' : C} (hz : orderOf z = 3) (hw : orderOf w = 7) (hzw : z * w = w * z)
    (hz' : orderOf z' = 3) (hw' : orderOf w' = 7) (hzw' : z' * w' = w' * z') :
    ∃ g : C, g * z * g⁻¹ = z' := by
  classical
  have hZ' : Nat.card ↥(center C) = 2 := hZ
  let π : C →* Perm (Fin 11) :=
    (alternatingGroup (Fin 11)).subtype.comp (E.toMonoidHom.comp (QuotientGroup.mk' (center C)))
  have hπker : π.ker = center C := by
    ext c
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : E (QuotientGroup.mk c) = 1 := Subtype.ext h
      have h2 : (QuotientGroup.mk c : C ⧸ center C) = 1 := (MulEquiv.map_eq_one_iff E).1 h1
      exact (QuotientGroup.eq_one_iff c).1 h2
    · intro h
      have h2 : (QuotientGroup.mk c : C ⧸ center C) = 1 := (QuotientGroup.eq_one_iff c).2 h
      have h1 : E (QuotientGroup.mk c) = 1 := by rw [h2, map_one]
      exact congrArg Subtype.val h1
  have hπA : ∀ c : C, π c ∈ alternatingGroup (Fin 11) := fun c => (E (QuotientGroup.mk c)).2
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    omega
  have hZeq : ∀ x ∈ center C, x = 1 ∨ x = t := fun x hx =>
    eq_one_or_eq_of_card_two hZ ht ht1 hx
  have himg : ∀ {q : ℕ} [Fact q.Prime] {x : C}, orderOf x = q → q ≠ 2 → orderOf (π x) = q := by
    intro q _ x hx hq2
    have hx1 : x ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hx
      exact (Fact.out : q.Prime).one_lt.ne hx
    have hxt : x ≠ t := by
      intro h
      rw [h, ht2] at hx
      exact hq2 hx.symm
    have hπx : π x ≠ 1 := by
      intro h
      have : x ∈ π.ker := h
      rw [hπker] at this
      rcases hZeq x this with h1 | h1
      · exact hx1 h1
      · exact hxt h1
    refine orderOf_eq_prime ?_ hπx
    rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have h3 : ∀ {x y : C}, orderOf x = 3 → orderOf y = 7 → x * y = y * x → (π x).IsThreeCycle := by
    intro x y hx hy hxy
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact threeCycle_of_comm_seven (himg hy (by norm_num)) (himg hx (by norm_num))
      (Commute.symm (by
        show π x * π y = π y * π x
        rw [← map_mul, ← map_mul, hxy]))
  have h3z := h3 hz hw hzw
  have h3z' := h3 hz' hw' hzw'
  obtain ⟨c, hc⟩ := isConj_iff.1 (alternatingGroup.isThreeCycle_isConj (by simp)
    (σ := ⟨π z, hπA z⟩) (τ := ⟨π z', hπA z'⟩) h3z h3z')
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (E.symm c)
  have hπq : π q = (c : Perm (Fin 11)) := by
    show ((E (QuotientGroup.mk q) : alternatingGroup (Fin 11)) : Perm (Fin 11)) = c
    rw [hq, MulEquiv.apply_symm_apply]
  refine ⟨q, ?_⟩
  have hker : q * z * q⁻¹ * z'⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hπq]
    have := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [this]
    group
  rw [hπker] at hker
  rcases hZeq _ hker with h | h
  · exact mul_inv_eq_one.1 h
  · exfalso
    have h1 : q * z * q⁻¹ = t * z' := by
      calc q * z * q⁻¹ = (q * z * q⁻¹ * z'⁻¹) * z' := by group
        _ = t * z' := by rw [h]
    have h2 : (q * z * q⁻¹) ^ 3 = 1 := by
      rw [conj_pow, show z ^ 3 = 1 by rw [← hz]; exact pow_orderOf_eq_one z]
      group
    have hz3 : z' ^ 3 = 1 := by rw [← hz']; exact pow_orderOf_eq_one z'
    have htc : Commute t z' := (Subgroup.mem_center_iff.1 ht z').symm
    have ht22 : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
    rw [h1, htc.mul_pow, hz3, mul_one] at h2
    have : t = 1 := by
      calc t = t ^ 3 := by rw [pow_succ, ht22, one_mul]
        _ = 1 := h2
    exact ht1 this

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.CoverConj
