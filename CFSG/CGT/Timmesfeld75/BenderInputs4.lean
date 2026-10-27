module

public import CFSG.CGT.Timmesfeld75.PaperSteps
import CFSG.Timmesfeld.Bridge.Asc72Bender

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.BenderSuzuki

section Basic

variable {K : Type*} [Group K]

theorem mem_normalizer_of_forall_mem_iff {Q T : Subgroup K}
    (hT : ∀ z, z ∈ T ↔ z ∈ Q ∧ ∀ q ∈ Q, Commute q z) {g : K}
    (hg : g ∈ Subgroup.normalizer (Q : Set K)) : g ∈ Subgroup.normalizer (T : Set K) := by
  have key : ∀ {g : K}, g ∈ Subgroup.normalizer (Q : Set K) → ∀ {z : K}, z ∈ T →
      g * z * g⁻¹ ∈ T := by
    intro g hg z hz
    obtain ⟨hzQ, hzc⟩ := (hT z).1 hz
    refine (hT _).2 ⟨(Subgroup.mem_normalizer_iff.1 hg z).1 hzQ, fun q hq => ?_⟩
    have hq' : g⁻¹ * q * g ∈ Q := by
      have h1 := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) q).1 hq
      rw [inv_inv] at h1
      exact h1
    have e1 : q * (g * z * g⁻¹) = g * ((g⁻¹ * q * g) * z) * g⁻¹ := by group
    have e2 : g * z * g⁻¹ * q = g * (z * (g⁻¹ * q * g)) * g⁻¹ := by group
    show q * (g * z * g⁻¹) = g * z * g⁻¹ * q
    rw [e1, e2, (hzc _ hq').eq]
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => key hg hh, fun hh => ?_⟩
  have h2 := key (inv_mem hg) hh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rw [e] at h2
  exact h2

variable [Finite K]

theorem mem_of_commute_sylow_of_strongWC (hK : IsBenderGroup K) {T : Subgroup K}
    (hT : StrongWC T) {x : K} (hx : x ∈ T) (hx1 : x ≠ 1) (Q : Sylow 2 K)
    (hTQ : T ≤ (Q : Subgroup K)) {z : K} (hzQ : z ∈ Q) (hzc : ∀ q ∈ Q, Commute q z) :
    z ∈ T := by
  rcases eq_or_ne z 1 with rfl | hz1
  · exact T.one_mem
  have hz2 : z * z = 1 :=
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.mul_self_eq_one_of_commute hK Q hzQ
      fun y hy => (hzc y hy).symm
  have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hxx : x * x = 1 := by rw [← pow_two]; exact hT.1.2 x hx
  have hxord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1
  obtain ⟨c, hc⟩ := isConj_iff.1
    (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isConj_of_orderOf_eq_two hK hxord hzord)
  have hcent : c⁻¹⁻¹ * x * c⁻¹ ∈ Subgroup.centralizer ({x} : Set K) := by
    rw [inv_inv, hc]
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hzc x (hTQ hx)
  have hmem := hT.2 x hx hx1 x hx c⁻¹ hcent
  rwa [inv_inv, hc] at hmem

end Basic

theorem benderTransitiveInput_of_repo : BenderTransitiveInput := by
  intro K _ _ T hT _ hK x hx hx1 y hy hy1
  obtain ⟨Q, hTQ⟩ := (isPGroup_two_of_isElemAbelian hT.1).exists_le_sylow
  have hcomm : ∀ t ∈ T, ∀ q ∈ Q, Commute t q := fun t ht q hq =>
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hK Q (hTQ ht)
      (by rw [← pow_two]; exact hT.1.2 t ht) q hq
  have hTcen : ∀ z ∈ T, ∀ q ∈ Q, Commute q z := fun z hz q hq => (hcomm z hz q hq).symm
  have hiff : ∀ z, z ∈ T ↔ z ∈ Q ∧ ∀ q ∈ Q, Commute q z := fun z =>
    ⟨fun hz => ⟨hTQ hz, hTcen z hz⟩, fun hz =>
      mem_of_commute_sylow_of_strongWC hK hT hx hx1 Q hTQ hz.1 hz.2⟩
  obtain ⟨g, hgN, hg⟩ := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_normalizer_conj hK Q
    ⟨hTQ hx, hTcen x hx⟩ hx1 ⟨hTQ hy, hTcen y hy⟩ hy1
  exact ⟨g, mem_normalizer_of_forall_mem_iff (Q := (Q : Subgroup K)) hiff hgN, hg⟩

end CFSG.CGT.Timmesfeld75
