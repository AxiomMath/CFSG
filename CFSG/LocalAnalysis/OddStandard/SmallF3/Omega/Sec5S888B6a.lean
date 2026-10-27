module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888B5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888B3g
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888GT2

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] {z : G} {K : Fin 4 → Subgroup G}

private lemma b6_mem_conjugate_iff {X : Type*} [Group X] {H : Subgroup X} {g x : X} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have h : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    simpa [h] using ha
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

private lemma b6_conjugate_subgroupOf {X : Type*} [Group X] (Hc : Subgroup X) (x : Hc)
    (A : Subgroup X) :
    CFSG.conjugate (A.subgroupOf Hc) x = (CFSG.conjugate A (x : X)).subgroupOf Hc := by
  ext u
  rw [Subgroup.mem_subgroupOf, b6_mem_conjugate_iff, b6_mem_conjugate_iff,
    Subgroup.mem_subgroupOf]
  simp

private lemma b6_coe_mem_zpowers {X : Type*} [Group X] (H : Subgroup X) {h c : H}
    (hc : c ∈ Subgroup.zpowers h) : (c : X) ∈ Subgroup.zpowers (h : X) := by
  have hm : (Subgroup.zpowers h).map H.subtype = Subgroup.zpowers (h : X) :=
    MonoidHom.map_zpowers H.subtype h
  rw [← hm, Subgroup.mem_map]
  exact ⟨c, hc, rfl⟩

theorem isSylow2Of_centralizer_of_quad [Finite G] (hq : Sec5B517Quad K z)
    (hNz : normalizer (Sec5B517Q8 hq : Set G) ≤ centralizer ({z} : Set G))
    (hperm : ∀ n ∈ normalizer (Sec5B517Q8 hq : Set G), ∀ i : Fin 4,
      ∃ j, CFSG.conjugate (K i) n = K j)
    (hcent : ∀ s ∈ normalizer (Sec5B517Q8 hq : Set G), s * s ∈ Sec5B517Q8 hq →
      (∀ q ∈ Sec5B517Q8 hq, s * q * s⁻¹ * q⁻¹ ∈ zpowers z) → s ∈ Sec5B517Q8 hq)
    (hparG : ∀ w ∈ normalizer (Sec5B517Q8 hq : Set G), (∀ i, CFSG.conjugate (K i) w = K i) →
      (∀ q ∈ Sec5B517Q8 hq, w * w * q * (w * w)⁻¹ * q⁻¹ ∈ zpowers z) →
        Even (Nat.card {i : Fin 4 // ∃ q ∈ twoCoreIn (K i),
          w⁻¹ * q * w ≠ q ∧ w⁻¹ * q * w ≠ q * z}))
    {T : Subgroup G} (hQT : Sec5B517Q8 hq ≤ T)
    (hTN : IsSylow2Of T (normalizer (Sec5B517Q8 hq : Set G))) :
    IsSylow2Of T (centralizer ({z} : Set G)) := by
  classical
  let Hc : Subgroup G := centralizer ({z} : Set G)
  have hz : z ∈ Hc := (zCent z).2
  have hK : ∀ i, K i ≤ Hc := fun i => le_centralizer_of_quad hq i
  have hQH : Sec5B517Q8 hq ≤ Hc := hQT.trans (hTN.1.trans hNz)
  have hTH : T ≤ Hc := hTN.1.trans hNz
  have hQ8 : Sec5B517Q8 (quad_subgroupOf hq hK hz) = (Sec5B517Q8 hq).subgroupOf Hc :=
    q8_subgroupOf hq hK hz
  have hzcenter : (⟨z, hz⟩ : Hc) ∈ Subgroup.center Hc := by
    change zCent z ∈ Subgroup.center Hc
    exact zCent_mem_center z
  haveI : (Subgroup.zpowers (⟨z, hz⟩ : Hc)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le_of_mem hzcenter)
  let α : Hc →* Hc ⧸ Subgroup.zpowers (⟨z, hz⟩ : Hc) := QuotientGroup.mk' _
  have hS : PlaneSetup (⟨z, hz⟩ : Hc) (fun i => (K i).subgroupOf Hc) α :=
    ⟨quad_subgroupOf hq hK hz, QuotientGroup.mk'_surjective _, QuotientGroup.ker_mk' _⟩
  have hperm' : ∀ x ∈ normalizer (Sec5B517Q8 (quad_subgroupOf hq hK hz) : Set Hc),
      ∀ i : Fin 4, ∃ j, CFSG.conjugate ((K i).subgroupOf Hc) x = (K j).subgroupOf Hc := by
    intro x hx i
    have hxN : (x : G) ∈ normalizer (Sec5B517Q8 hq : Set G) := by
      rw [hQ8, ← Subgroup.subgroupOf_normalizer_eq hQH] at hx
      exact Subgroup.mem_subgroupOf.1 hx
    obtain ⟨j, hj⟩ := hperm (x : G) hxN i
    exact ⟨j, by rw [b6_conjugate_subgroupOf Hc x (K i), hj]⟩
  have hcent' : ∀ s ∈ normalizer (Sec5B517Q8 (quad_subgroupOf hq hK hz) : Set Hc),
      s * s ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz) →
      (∀ q ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz),
        s * q * s⁻¹ * q⁻¹ ∈ zpowers (⟨z, hz⟩ : Hc)) →
      s ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz) := by
    intro s hs hs2 hcomm
    have hsN : (s : G) ∈ normalizer (Sec5B517Q8 hq : Set G) := by
      rw [hQ8, ← Subgroup.subgroupOf_normalizer_eq hQH] at hs
      exact Subgroup.mem_subgroupOf.1 hs
    have hs2' : (s : G) * (s : G) ∈ Sec5B517Q8 hq := by
      rw [hQ8, Subgroup.mem_subgroupOf] at hs2
      simpa using hs2
    have hcommG : ∀ q ∈ Sec5B517Q8 hq,
        (s : G) * q * (s : G)⁻¹ * q⁻¹ ∈ Subgroup.zpowers z := by
      intro q hqQ
      have hqH : q ∈ Hc := hQH hqQ
      have hmem : (⟨q, hqH⟩ : Hc) ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz) := by
        rw [hQ8]
        exact hqQ
      have h := hcomm (⟨q, hqH⟩ : Hc) hmem
      have h' := b6_coe_mem_zpowers Hc h
      simpa using h'
    have hsQ : (s : G) ∈ Sec5B517Q8 hq := hcent (s : G) hsN hs2' hcommG
    rw [hQ8, Subgroup.mem_subgroupOf]
    exact hsQ
  have hpar' : ∀ w ∈ normalizer (Sec5B517Q8 (quad_subgroupOf hq hK hz) : Set Hc),
      (∀ i, CFSG.conjugate ((K i).subgroupOf Hc) w = (K i).subgroupOf Hc) →
      (∀ q ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz),
        w * w * q * (w * w)⁻¹ * q⁻¹ ∈ zpowers (⟨z, hz⟩ : Hc)) →
      Even (Nat.card {i : Fin 4 // ∃ q ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz) ⊓
        (K i).subgroupOf Hc, w⁻¹ * q * w ≠ q ∧
        w⁻¹ * q * w ≠ q * (⟨z, hz⟩ : Hc)}) :=
    parity_subgroupOf hq hK hz hparG
  have hQT' : Sec5B517Q8 (quad_subgroupOf hq hK hz) ≤ T.subgroupOf Hc := by
    rw [hQ8]
    exact Subgroup.subgroupOf_mono Hc hQT
  have hTN' : IsSylow2Of (T.subgroupOf Hc)
      (normalizer (Sec5B517Q8 (quad_subgroupOf hq hK hz) : Set Hc)) := by
    rw [hQ8, ← Subgroup.subgroupOf_normalizer_eq hQH]
    refine ⟨Subgroup.subgroupOf_mono Hc hTN.1, ?_, ?_⟩
    · exact hTN.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
    · rw [Subgroup.relIndex_subgroupOf hNz]
      exact hTN.2.2
  have hTop : IsSylow2Of (T.subgroupOf Hc) (⊤ : Subgroup Hc) :=
    isSylow2Of_top_of_setup hS hperm' hcent' hpar' hQT' hTN'
  refine ⟨hTH, hTN.2.1, ?_⟩
  rw [show T.relIndex Hc = (T.subgroupOf Hc).relIndex (⊤ : Subgroup Hc) by
    rw [Subgroup.relIndex_top_right]
    rfl]
  exact hTop.2.2

end CFSG.OddStandard.SmallF3.Omega
