module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888B3a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888GT1

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] {z : G} {K : Fin 4 → Subgroup G}

private lemma s888b3g_mem_conjugate_iff {X : Type*} [Group X] {H : Subgroup X} {g x : X} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have h : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    simpa [h] using ha
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

private lemma s888b3g_conjugate_subgroupOf {X : Type*} [Group X] (Hc : Subgroup X) (x : Hc)
    (A : Subgroup X) :
    CFSG.conjugate (A.subgroupOf Hc) x = (CFSG.conjugate A (x : X)).subgroupOf Hc := by
  ext u
  rw [Subgroup.mem_subgroupOf, s888b3g_mem_conjugate_iff, s888b3g_mem_conjugate_iff,
    Subgroup.mem_subgroupOf]
  simp

private lemma s888b3g_coe_mem_zpowers {X : Type*} [Group X] (H : Subgroup X) {h c : H}
    (hc : c ∈ Subgroup.zpowers h) : (c : X) ∈ Subgroup.zpowers (h : X) := by
  have hm : (Subgroup.zpowers h).map H.subtype = Subgroup.zpowers (h : X) :=
    MonoidHom.map_zpowers H.subtype h
  rw [← hm, Subgroup.mem_map]
  exact ⟨c, hc, rfl⟩

private lemma s888b3g_all_le {Hc : Subgroup G} (hK : ∀ i, K i ≤ Hc) :
    Sec5B517All K ≤ Hc :=
  sup_le (sup_le (sup_le (hK 0) (hK 1)) (hK 2)) (hK 3)

private lemma s888b3g_conjugate_le {Hc : Subgroup G} {w : Hc} {A : Subgroup G}
    (hA : A ≤ Hc) : CFSG.conjugate A (w : G) ≤ Hc := by
  intro x hx
  rw [s888b3g_mem_conjugate_iff] at hx
  have hxH : (w : G) * x * (w : G)⁻¹ ∈ Hc := hA hx
  have hx' : x = (w : G)⁻¹ * ((w : G) * x * (w : G)⁻¹) * (w : G) := by group
  rw [hx']
  exact Hc.mul_mem (Hc.mul_mem (Hc.inv_mem w.2) hxH) w.2

theorem parity_subgroupOf [Finite G] (hq : Sec5B517Quad K z) {Hc : Subgroup G}
    (hK : ∀ i, K i ≤ Hc) (hz : z ∈ Hc)
    (hparG : ∀ w ∈ normalizer (Sec5B517Q8 hq : Set G), (∀ i, CFSG.conjugate (K i) w = K i) →
      (∀ q ∈ Sec5B517Q8 hq, w * w * q * (w * w)⁻¹ * q⁻¹ ∈ zpowers z) →
        Even (Nat.card {i : Fin 4 // ∃ q ∈ twoCoreIn (K i),
          w⁻¹ * q * w ≠ q ∧ w⁻¹ * q * w ≠ q * z})) :
    ∀ w ∈ normalizer (Sec5B517Q8 (quad_subgroupOf hq hK hz) : Set Hc),
      (∀ i, CFSG.conjugate ((K i).subgroupOf Hc) w = (K i).subgroupOf Hc) →
      (∀ q ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz),
        w * w * q * (w * w)⁻¹ * q⁻¹ ∈ zpowers (⟨z, hz⟩ : Hc)) →
        Even (Nat.card {i : Fin 4 // ∃ q ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz) ⊓
          (K i).subgroupOf Hc, w⁻¹ * q * w ≠ q ∧ w⁻¹ * q * w ≠ q * (⟨z, hz⟩ : Hc)}) := by
  intro w hwN hwconj hwcomm
  have hAllH : Sec5B517All K ≤ Hc := s888b3g_all_le hK
  have hQH : Sec5B517Q8 hq ≤ Hc := (Sec5B517Q8.le_all hq).trans hAllH
  have hQ8 : Sec5B517Q8 (quad_subgroupOf hq hK hz) = (Sec5B517Q8 hq).subgroupOf Hc :=
    q8_subgroupOf hq hK hz
  have hwN' : (w : G) ∈ normalizer (Sec5B517Q8 hq : Set G) := by
    rw [hQ8, ← Subgroup.subgroupOf_normalizer_eq hQH] at hwN
    exact Subgroup.mem_subgroupOf.1 hwN
  have hwconj' : ∀ i, CFSG.conjugate (K i) (w : G) = K i := by
    intro i
    have h := s888b3g_conjugate_subgroupOf Hc w (K i)
    have hconj := hwconj i
    rw [h] at hconj
    have hinf := Subgroup.subgroupOf_inj.mp hconj
    rw [inf_eq_left.mpr (s888b3g_conjugate_le (hK i)), inf_eq_left.mpr (hK i)] at hinf
    exact hinf
  have hwcomm' : ∀ q ∈ Sec5B517Q8 hq,
      (w : G) * (w : G) * q * ((w : G) * (w : G))⁻¹ * q⁻¹ ∈ zpowers z := by
    intro q hqQ
    have hqH : q ∈ Hc := hQH hqQ
    have hmem : (⟨q, hqH⟩ : Hc) ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz) := by
      rw [hQ8]
      exact Subgroup.mem_subgroupOf.2 hqQ
    have h := hwcomm (⟨q, hqH⟩ : Hc) hmem
    have h' := s888b3g_coe_mem_zpowers Hc h
    simpa using h'
  have hpar := hparG (w : G) hwN' hwconj' hwcomm'
  have hiff : ∀ i : Fin 4,
      (∃ q : G, q ∈ twoCoreIn (K i) ∧
        (w : G)⁻¹ * q * (w : G) ≠ q ∧ (w : G)⁻¹ * q * (w : G) ≠ q * z) ↔
      (∃ q : Hc, q ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz) ⊓ (K i).subgroupOf Hc ∧
        w⁻¹ * q * w ≠ q ∧ w⁻¹ * q * w ≠ q * (⟨z, hz⟩ : Hc)) := by
    intro i
    rw [twoCoreIn_eq_inf hq i, hQ8]
    constructor
    · rintro ⟨q, hqmem, h1, h2⟩
      have hqH : q ∈ Hc := hK i hqmem.2
      refine ⟨⟨q, hqH⟩, ⟨?_, ?_⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.2 hqmem.1
      · exact Subgroup.mem_subgroupOf.2 hqmem.2
      · intro hh
        exact h1 (by simpa using Subtype.ext_iff.mp hh)
      · intro hh
        exact h2 (by simpa using Subtype.ext_iff.mp hh)
    · rintro ⟨q, hqmem, h1, h2⟩
      refine ⟨(q : G), ⟨?_, ?_⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.1 hqmem.1
      · exact Subgroup.mem_subgroupOf.1 hqmem.2
      · intro hh
        exact h1 (Subtype.ext hh)
      · intro hh
        exact h2 (Subtype.ext hh)
  have hcard := Nat.card_congr (Equiv.subtypeEquivRight hiff)
  rw [hcard] at hpar
  exact hpar

end CFSG.OddStandard.SmallF3.Omega
