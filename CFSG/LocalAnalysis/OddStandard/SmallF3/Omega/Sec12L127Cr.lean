module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L127Nat

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped Pointwise

variable {G : Type} [Group G]

namespace Sec127NatCoord

variable {V1 X : Subgroup G} {φ : (Fin 5 → ZMod 2) → G}

theorem exists_involution_perm (hc : Sec127NatCoord V1 X φ)
    (hA5 : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5)))) {u : G} (hu : u ∈ X) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) :
    ∃ σ ∈ alternatingGroup (Fin 5), σ ≠ 1 ∧
      (∀ v, IsEvenVec v → permVec σ (permVec σ v) = v) ∧
      ∀ v, IsEvenVec v → u * φ v * u⁻¹ = φ (permVec σ v) := by
  obtain ⟨σ, hσ, hact⟩ := hc.act u hu
  refine ⟨σ, hσ, ?_, ?_, hact⟩
  · rintro rfl
    apply hu1
    have hcent : u ∈ centralizer (V1 : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨v, hv, rfl⟩ := hc.surj x hx
      have h1 := hact v hv
      have h2 : u * φ v * u⁻¹ = φ v := by
        rw [h1]
        rfl
      calc φ v * u = (u * φ v * u⁻¹) * u := by rw [h2]
        _ = u * φ v := by group
    have hbot := sec127_nat_cent_bot hc hA5
    have hmem : u ∈ X ⊓ centralizer (V1 : Set G) := Subgroup.mem_inf.mpr ⟨hu, hcent⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  · intro v hv
    have hv' := sec127_isEvenVec_permVec σ hv
    have hv'' := sec127_isEvenVec_permVec σ hv'
    apply (hc.eq_iff hv'' hv).mp
    rw [← hact _ hv', ← hact v hv]
    have hinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    rw [hinv]
    calc u * (u * φ v * u) * u = (u * u) * φ v * (u * u) := by group
      _ = φ v := by rw [hu2]; group

theorem comm_range (hc : Sec127NatCoord V1 X φ)
    (hA5 : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5)))) {u : G} (hu : u ∈ X) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) {d : G} (hd : d ∈ V1) (hdu : u * d * u⁻¹ = d) :
    ∃ v ∈ V1, u * v * u⁻¹ * v⁻¹ = d := by
  obtain ⟨σ, hσ, hne, hsq, hact⟩ := hc.exists_involution_perm hA5 hu hu2 hu1
  obtain ⟨w, hw, rfl⟩ := hc.surj d hd
  have hfix : permVec σ w = w := by
    apply (hc.eq_iff (sec127_isEvenVec_permVec σ hw) hw).mp
    rw [← hact w hw]
    exact hdu
  obtain ⟨w', hw', hw'eq⟩ := sec127_perm_decide σ hσ hne hsq w hw hfix
  refine ⟨φ w', hc.mem w' hw', ?_⟩
  rw [← hw'eq, hc.mul _ _ (sec127_isEvenVec_permVec σ hw') hw', ← hact w' hw']
  have hinv : (φ w')⁻¹ = φ w' := inv_eq_of_mul_eq_one_right (hc.mul_self hw')
  rw [hinv]

end Sec127NatCoord

theorem sec127_mem_sup_mul {V V1 V2 : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V)
    (h1 : V1 ≤ V) (h2 : V2 ≤ V) {d : G} (hd : d ∈ V1 ⊔ V2) :
    ∃ d1 ∈ V1, ∃ d2 ∈ V2, d1 * d2 = d := by
  have hN : V2 ≤ normalizer (V1 : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      hV.comm (h1 hy) (h2 hx))
  have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left V1 V2 hN
  have hd' : d ∈ ((V1 : Set G) * (V2 : Set G)) := by
    rw [← hcoe]
    exact hd
  obtain ⟨d1, hd1, d2, hd2, h⟩ := Set.mem_mul.mp hd'
  exact ⟨d1, hd1, d2, hd2, h⟩

theorem sec127_decomp_unique {V1 V2 : Subgroup G} (hinf : V1 ⊓ V2 = ⊥) {a1 b1 a2 b2 : G}
    (ha1 : a1 ∈ V1) (hb1 : b1 ∈ V1) (ha2 : a2 ∈ V2) (hb2 : b2 ∈ V2) (h : a1 * a2 = b1 * b2) :
    a1 = b1 ∧ a2 = b2 := by
  have h1 : b1⁻¹ * a1 = b2 * a2⁻¹ := by
    calc b1⁻¹ * a1 = b1⁻¹ * (a1 * a2) * a2⁻¹ := by group
      _ = b1⁻¹ * (b1 * b2) * a2⁻¹ := by rw [h]
      _ = b2 * a2⁻¹ := by group
  have hmem : b1⁻¹ * a1 ∈ V1 ⊓ V2 := by
    refine Subgroup.mem_inf.mpr ⟨V1.mul_mem (V1.inv_mem hb1) ha1, ?_⟩
    rw [h1]
    exact V2.mul_mem hb2 (V2.inv_mem ha2)
  rw [hinf, Subgroup.mem_bot] at hmem
  have e1 : a1 = b1 := by
    calc a1 = b1 * (b1⁻¹ * a1) := by group
      _ = b1 := by rw [hmem, mul_one]
  refine ⟨e1, ?_⟩
  rw [e1] at h
  exact mul_left_cancel h

theorem sec127_comm_range {V V1 V2 X : Subgroup G} {φ1 φ2 : (Fin 5 → ZMod 2) → G}
    (hV : CFSG.Open.IsElemAbelian 2 V) (hsup : V1 ⊔ V2 = V) (hinf : V1 ⊓ V2 = ⊥)
    (hc1 : Sec127NatCoord V1 X φ1) (hc2 : Sec127NatCoord V2 X φ2)
    (hA5 : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5)))) {u : G} (hu : u ∈ X) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) {d : G} (hdV : d ∈ V) (hdu : u * d = d * u) :
    ∃ v ∈ V, u * v * u⁻¹ * v⁻¹ = d := by
  have h1V : V1 ≤ V := le_trans le_sup_left hsup.le
  have h2V : V2 ≤ V := le_trans le_sup_right hsup.le
  obtain ⟨d1, hd1, d2, hd2, hd⟩ := sec127_mem_sup_mul hV h1V h2V (hsup.ge hdV)
  have hn1 : ∀ x ∈ V1, u * x * u⁻¹ ∈ V1 := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc1.normalizes hu) x).mp hx
  have hn2 : ∀ x ∈ V2, u * x * u⁻¹ ∈ V2 := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc2.normalizes hu) x).mp hx
  have hconj : (u * d1 * u⁻¹) * (u * d2 * u⁻¹) = d1 * d2 := by
    have h3 : u * d * u⁻¹ = d := by
      calc u * d * u⁻¹ = d * u * u⁻¹ := by rw [hdu]
        _ = d := by group
    calc (u * d1 * u⁻¹) * (u * d2 * u⁻¹) = u * (d1 * d2) * u⁻¹ := by group
      _ = u * d * u⁻¹ := by rw [hd]
      _ = d := h3
      _ = d1 * d2 := hd.symm
  obtain ⟨e1, e2⟩ := sec127_decomp_unique hinf (hn1 d1 hd1) hd1 (hn2 d2 hd2) hd2 hconj
  obtain ⟨v1, hv1, hv1c⟩ := hc1.comm_range hA5 hu hu2 hu1 hd1 e1
  obtain ⟨v2, hv2, hv2c⟩ := hc2.comm_range hA5 hu hu2 hu1 hd2 e2
  have hv1V : v1 ∈ V := h1V hv1
  have hv2V : v2 ∈ V := h2V hv2
  refine ⟨v1 * v2, V.mul_mem hv1V hv2V, ?_⟩
  have hx2 : u * v2 * u⁻¹ ∈ V := h2V (hn2 v2 hv2)
  have hcomm : v1⁻¹ * (u * v2 * u⁻¹ * v2⁻¹) = (u * v2 * u⁻¹ * v2⁻¹) * v1⁻¹ :=
    hV.comm (V.inv_mem hv1V) (V.mul_mem hx2 (V.inv_mem hv2V))
  rw [← hd, ← hv1c, ← hv2c]
  calc u * (v1 * v2) * u⁻¹ * (v1 * v2)⁻¹
      = (u * v1 * u⁻¹) * (u * v2 * u⁻¹ * v2⁻¹) * v1⁻¹ := by group
    _ = (u * v1 * u⁻¹) * (v1⁻¹ * (u * v2 * u⁻¹ * v2⁻¹)) := by rw [hcomm]; group
    _ = (u * v1 * u⁻¹ * v1⁻¹) * (u * v2 * u⁻¹ * v2⁻¹) := by group

end CFSG.OddStandard.SmallF3.Omega
