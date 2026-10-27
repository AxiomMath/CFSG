module

public import CFSG.HardMathSupport.Foote.E27.Split

public section

namespace CFSG.HardMathSupport.Foote.E27

open Subgroup

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem E27Config.card_le_twentyseven_of_isPGroup (h : E27Config X K R T z)
    {Q : Subgroup X} (hQ : Q ≤ centralizer ({z} : Set X)) (hQ3 : IsPGroup 3 Q) :
    Nat.card Q ≤ 27 := by
  obtain ⟨S, hS⟩ := h.sylow
  have hQ1 : IsPGroup 3 (Q.subgroupOf (centralizer ({z} : Set X))) := hQ3.comap_subtype
  obtain ⟨P, hP⟩ := hQ1.exists_le_sylow
  have h1 : Nat.card (Q.subgroupOf (centralizer ({z} : Set X))) ≤ Nat.card P :=
    Subgroup.card_le_of_le hP
  have h2 : Nat.card (Q.subgroupOf (centralizer ({z} : Set X))) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ).toEquiv
  have h3 : Nat.card P = Nat.card S := by
    rw [Sylow.card_eq_multiplicity P, Sylow.card_eq_multiplicity S]
  have h4 : Nat.card (S : Subgroup ↥(centralizer ({z} : Set X))) = 27 := by
    rw [← h.card_R, ← hS]
    exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
  omega

theorem E27Config.isSylow_centralizer_of_mem (h : E27Config X K R T z) (hz : z ∈ K) :
    ∃ S : Sylow 3 ↥(centralizer ({z} : Set X) ⊓ K),
      Subgroup.map (centralizer ({z} : Set X) ⊓ K).subtype
        (S : Subgroup ↥(centralizer ({z} : Set X) ⊓ K)) = R := by
  set D := centralizer ({z} : Set X) ⊓ K with hD
  have hRD : R ≤ D := by
    refine le_inf ?_ (h.le_of_mem hz)
    intro t ht
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      (h.elem.1.is_comm.comm (⟨t, ht⟩ : R) ⟨z, h.z_mem⟩)
  let R' : Subgroup ↥D := R.subgroupOf D
  have hR'card : Nat.card R' = 27 := by
    rw [← h.card_R]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRD).toEquiv
  have hR'p : IsPGroup 3 R' := by
    have : Nat.card R' = 3 ^ 3 := by rw [hR'card]; norm_num
    exact IsPGroup.of_card this
  obtain ⟨Q, hQ⟩ := hR'p.exists_le_sylow
  have hQp : IsPGroup 3 (Subgroup.map D.subtype (Q : Subgroup ↥D)) := Q.isPGroup'.map _
  have hQle : Nat.card (Subgroup.map D.subtype (Q : Subgroup ↥D)) ≤ 27 :=
    h.card_le_twentyseven_of_isPGroup (by rintro _ ⟨x, -, rfl⟩; exact x.2.1) hQp
  have hQcard : Nat.card (Q : Subgroup ↥D) ≤ 27 := by
    rwa [Subgroup.card_map_of_injective D.subtype_injective] at hQle
  have hQeq : R' = (Q : Subgroup ↥D) :=
    Subgroup.eq_of_le_of_card_ge hQ (by omega)
  refine ⟨Q, ?_⟩
  rw [← hQeq]
  exact Subgroup.map_subgroupOf_eq_of_le hRD

theorem E27Config.factorization_card_centralizer_inf_of_mem (h : E27Config X K R T z)
    (hz : z ∈ K) :
    (Nat.card ↥(centralizer ({z} : Set X) ⊓ K)).factorization 3 = 3 := by
  obtain ⟨S, hS⟩ := h.isSylow_centralizer_of_mem hz
  have h1 := Sylow.card_eq_multiplicity S
  have h2 : Nat.card (S : Subgroup ↥(centralizer ({z} : Set X) ⊓ K)) = 27 := by
    rw [← h.card_R, ← hS]
    exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
  rw [h2] at h1
  have h27 : (27 : ℕ) = 3 ^ 3 := by norm_num
  rw [h27] at h1
  exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1).symm

end CFSG.HardMathSupport.Foote.E27
