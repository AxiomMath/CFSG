module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem sec8t84d5_isSylow2Of_sup_of_normal_odd {E Q N : Subgroup G}
    (hEN : E ≤ N) (hE2 : IsPGroup 2 E) (hQN : Q ≤ N)
    (hQn : (Q.subgroupOf N).Normal) (hQodd : Odd (Nat.card Q)) :
    IsSylow2Of E (E ⊔ Q) := by
  have hEM : E ≤ E ⊔ Q := le_sup_left
  have hQM : Q ≤ E ⊔ Q := le_sup_right
  have hQnormM : (Q.subgroupOf (E ⊔ Q)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQM]
    exact (sup_le hEN hQN).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hQN).mp hQn)
  have hdisj : Disjoint E Q := by
    apply IsPGroup.disjoint_of_coprime hE2 (IsPGroup.card (G := Q))
    exact Nat.coprime_two_left.mpr hQodd
  haveI : (Q.subgroupOf (E ⊔ Q)).Normal := hQnormM
  have h1 : (Q.subgroupOf (E ⊔ Q)).index = Q.relIndex E := by
    have h := Subgroup.relIndex_sup_right (H := E.subgroupOf (E ⊔ Q))
      (K := Q.subgroupOf (E ⊔ Q))
    rw [← Subgroup.subgroupOf_sup hEM hQM, Subgroup.subgroupOf_self,
      Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hEM] at h
    exact h
  have h2 : Q.relIndex E = Nat.card E := by
    have h := Subgroup.relIndex_mul_card (H := Q) (K := E)
    rw [show Q ⊓ E = ⊥ by rw [inf_comm]; exact disjoint_iff.mp hdisj, Subgroup.card_bot,
      mul_one] at h
    exact h
  have hQrel : Q.relIndex (E ⊔ Q) = Nat.card E := h1.trans h2
  have hcard : Nat.card ↥(E ⊔ Q) = Nat.card E * Nat.card Q := by
    have h := Subgroup.relIndex_mul_card (H := Q) (K := E ⊔ Q)
    rw [inf_eq_left.mpr hQM, hQrel] at h
    exact h.symm
  have hErel : E.relIndex (E ⊔ Q) = Nat.card Q := by
    have h := Subgroup.relIndex_mul_card (H := E) (K := E ⊔ Q)
    rw [inf_eq_left.mpr hEM, hcard, mul_comm (Nat.card E) (Nat.card Q)] at h
    exact Nat.mul_right_cancel (Nat.card_pos (α := ↥E)) h
  exact ⟨hEM, hE2, by rw [hErel]; exact hQodd.not_two_dvd_nat⟩

theorem sec8t84d5_isSylow2Of_map_conj {S H : Subgroup G}
    (h : IsSylow2Of S H) {v : G} (hv : v ∈ Subgroup.normalizer (H : Set G)) :
    IsSylow2Of (S.map (MulAut.conj v).toMonoidHom) H := by
  have hmapH : H.map (MulAut.conj v).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hv
  refine ⟨?_, h.2.1.map _, ?_⟩
  · rw [← hmapH]; exact Subgroup.map_mono h.1
  · rw [← hmapH, Subgroup.relIndex_map_map_of_injective (H := S) (K := H)
      (MulAut.conj v).injective]
    exact h.2.2

theorem sec8t84d5_exists_mul_mem_sup_normalizer {S H : Subgroup G}
    (hS : IsSylow2Of S H) {v : G} (hv : v ∈ Subgroup.normalizer (H : Set G)) :
    ∃ a ∈ H, a⁻¹ * v ∈ Subgroup.normalizer (S : Set G) := by
  have hconj : IsSylow2Of (S.map (MulAut.conj v).toMonoidHom) H :=
    sec8t84d5_isSylow2Of_map_conj hS hv
  obtain ⟨a, ha, hae⟩ := hS.exists_conj_mem hconj
  refine ⟨a, ha, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [show (a⁻¹ * v) * x * (a⁻¹ * v)⁻¹ = a⁻¹ * (v * x * v⁻¹) * a by group,
    ← hae (v * x * v⁻¹)]
  exact (Subgroup.mem_map_iff_mem (MulAut.conj v).injective).symm

theorem sec8t84d5_conj_mem_normalizer {H : Subgroup G} {t x : G}
    (ht : t ∈ Subgroup.normalizer (H : Set G)) (hx : x ∈ Subgroup.normalizer (H : Set G)) :
    t * x * t⁻¹ ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro e
  constructor
  · intro he
    have h1 : t⁻¹ * e * t ∈ H := (Subgroup.mem_normalizer_iff''.mp ht e).mp he
    have h2 : x * (t⁻¹ * e * t) * x⁻¹ ∈ H := (hx _).mp h1
    have h3 : t * (x * (t⁻¹ * e * t) * x⁻¹) * t⁻¹ ∈ H := (ht _).mp h2
    convert h3 using 1
    group
  · intro he
    have h3 : t * (x * (t⁻¹ * e * t) * x⁻¹) * t⁻¹ ∈ H := by
      convert he using 1
      group
    have h2 : x * (t⁻¹ * e * t) * x⁻¹ ∈ H := (ht _).mpr h3
    exact (Subgroup.mem_normalizer_iff''.mp ht e).mpr ((hx _).mpr h2)

end CFSG.OddStandard.SmallF3.Omega
