module

public import CFSG.HardMathSupport.Foote.E27.Defs
public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge

public section

namespace CFSG.HardMathSupport.Curtis.Proving

open CFSG.HardMathSupport.Foote.E27 CFSG.Open CFSG.LieType.SeitzGeneration Subgroup

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem sup_le_R (h : E27Config X K R T z) : T ⊔ Subgroup.zpowers z ≤ R :=
  sup_le h.T_le_R (Subgroup.zpowers_le.2 h.z_mem)

theorem sup_le_K (h : E27Config X K R T z) (hz : z ∈ K) : T ⊔ Subgroup.zpowers z ≤ K :=
  sup_le h.T_le_K (Subgroup.zpowers_le.2 hz)

theorem card_sup_eq (h : E27Config X K R T z) :
    Nat.card (T ⊔ Subgroup.zpowers z : Subgroup X) = 27 := by
  set S : Subgroup X := T ⊔ Subgroup.zpowers z with hSdef
  have hTS : T ≤ S := le_sup_left
  have hzS : z ∈ S := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hSR : S ≤ R := sup_le_R h
  have hT9 : Nat.card T = 9 := h.card_T
  have hS27 : Nat.card S ∣ 3 ^ 3 := by
    have h1 := Subgroup.card_dvd_of_le hSR
    rw [h.card_R] at h1
    norm_num
    exact h1
  have hSge : 9 ≤ Nat.card S := by
    have h1 := Subgroup.card_dvd_of_le hTS
    rw [hT9] at h1
    exact Nat.le_of_dvd Nat.card_pos h1
  have hSne9 : Nat.card S ≠ 9 := by
    intro e
    have hTS' : T = S :=
      Subgroup.eq_of_le_of_card_ge hTS (by rw [e, hT9])
    apply h.z_not_mem
    rw [hTS']
    exact hzS
  obtain ⟨m, hm, hmS⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hS27
  have key : ∀ m : ℕ, m ≤ 3 → 9 ≤ 3 ^ m → 3 ^ m ≠ 9 → 3 ^ m = 27 := by
    intro m hm
    interval_cases m <;> decide
  rw [hmS] at hSge hSne9 ⊢
  exact key m hm hSge hSne9

theorem false_of_E27_rankLE2 (h : E27Config X K R T z) (hz : z ∈ K)
    (hr : RankLE2 3 ↥K) : False := by
  have hSK : T ⊔ Subgroup.zpowers z ≤ K := sup_le_K h hz
  have hRK : IsElemAbelian 3 (R.comap K.subtype) :=
    isElemAbelian_comap_of_injective K.subtype K.subtype_injective h.elem
  have hQ : (T ⊔ Subgroup.zpowers z).subgroupOf K ≤ R.comap K.subtype := fun x hx =>
    sup_le_R h (Subgroup.mem_subgroupOf.1 hx)
  have hel : IsElemAbelian 3 ((T ⊔ Subgroup.zpowers z).subgroupOf K) :=
    isElemAbelian_of_le hQ hRK
  have hcard : Nat.card ((T ⊔ Subgroup.zpowers z).subgroupOf K) = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv, card_sup_eq h]
  have hle := hr _ hel
  rw [hcard] at hle
  norm_num at hle

end CFSG.HardMathSupport.Curtis.Proving
